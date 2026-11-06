import NetHack.Soko22Hazard87.AndIntroBlocks0248
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro62250 (p : Pattern) (ha : d26064 p = 1) (hb : d152855 p = 1) : d157097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26059 q = 1) (hb : d152855 q = 1) : d157092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26059, d157092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62249 q ha hb
    | true =>
      simp only [d26059, d157092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26060 q = 1) (hb : d152855 q = 1) : d157093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26060, d157093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26060, d157093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26061 q = 1) (hb : d152855 q = 1) : d157094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26061, d157094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26061, d157094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26062 q = 1) (hb : d152855 q = 1) : d157095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26062, d157095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26062, d157095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26063 q = 1) (hb : d152855 q = 1) : d157096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26063, d157096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26063, d157096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26064 q = 1) (hb : d152855 q = 1) : d157097 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26064, d157097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26064, d157097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62251 (p : Pattern) (ha : d25745 p = 1) (hb : d152855 p = 1) : d248705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d152855 q = 1) : d248680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62235 q ha hb
    | true =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d152855 q = 1) : d248681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d152855 q = 1) : d248682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d152855 q = 1) : d248683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d248683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d248683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25744 q = 1) (hb : d152855 q = 1) : d248704 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25744, d248704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25744, d248704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25745 q = 1) (hb : d152855 q = 1) : d248705 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25745, d248705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25745, d248705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62252 (p : Pattern) (ha : d25747 p = 1) (hb : d152855 p = 1) : d156921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d152855 q = 1) : d156896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25746 q = 1) (hb : d152855 q = 1) : d156920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25746, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25746, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25747 q = 1) (hb : d152855 q = 1) : d156921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25747, d156921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25747, d156921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62253 (p : Pattern) (ha : d25754 p = 1) (hb : d152855 p = 1) : d248712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d152855 q = 1) : d248680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62235 q ha hb
    | true =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d152855 q = 1) : d248681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d152855 q = 1) : d248682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25752 q = 1) (hb : d152855 q = 1) : d248710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25752, d248710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25752, d248710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25753 q = 1) (hb : d152855 q = 1) : d248711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25753, d248711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25753, d248711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25754 q = 1) (hb : d152855 q = 1) : d248712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25754, d248712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25754, d248712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62254 (p : Pattern) (ha : d25757 p = 1) (hb : d152855 p = 1) : d156931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25755 q = 1) (hb : d152855 q = 1) : d156929 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25755, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25755, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25756 q = 1) (hb : d152855 q = 1) : d156930 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25756, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25756, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25757 q = 1) (hb : d152855 q = 1) : d156931 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25757, d156931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25757, d156931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62255 (p : Pattern) (ha : d25770 p = 1) (hb : d152854 p = 1) : d248716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25763 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25769 q = 1) (hb : d152852 q = 1) : d25769 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25770 q = 1) (hb : d152854 q = 1) : d248716 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25770, d152854, d248716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25770, d152854, d248716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62256 (p : Pattern) (ha : d25775 p = 1) (hb : d152854 p = 1) : d248721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25450 q = 1) (hb : d152852 q = 1) : d25450 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25775 q = 1) (hb : d152854 q = 1) : d248721 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25775, d152854, d248721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25775, d152854, d248721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62257 (p : Pattern) (ha : d25789 p = 1) (hb : d152855 p = 1) : d248727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25771 q = 1) (hb : d152854 q = 1) : d248717 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25771, d248717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62255 q ha hb
    | true =>
      simp only [d25771, d248717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25772 q = 1) (hb : d152854 q = 1) : d248718 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25772, d248718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25772, d248718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25773 q = 1) (hb : d152854 q = 1) : d248719 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25773, d248719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25773, d248719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25774 q = 1) (hb : d152854 q = 1) : d248720 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25774, d248720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25774, d248720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25776 q = 1) (hb : d152854 q = 1) : d248722 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25776, d248722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62256 q ha hb
    | true =>
      simp only [d25776, d248722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25777 q = 1) (hb : d152854 q = 1) : d248723 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25777, d248723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25777, d248723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25778 q = 1) (hb : d152854 q = 1) : d248724 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25778, d248724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25778, d248724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25779 q = 1) (hb : d152854 q = 1) : d248725 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25779, d248725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25779, d248725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25780 q = 1) (hb : d152854 q = 1) : d248726 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25780, d248726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25780, d248726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25788 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25789 q = 1) (hb : d152855 q = 1) : d248727 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25789, d152855, d248727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25789, d152855, d248727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62258 (p : Pattern) (ha : d25451 p = 1) (hb : d152854 p = 1) : d248589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25450 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25220 q = 1) (hb : d152852 q = 1) : d25220 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25451 q = 1) (hb : d152854 q = 1) : d248589 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25451, d152854, d248589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25451, d152854, d248589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62259 (p : Pattern) (ha : d25793 p = 1) (hb : d152855 p = 1) : d248732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25452 q = 1) (hb : d152854 q = 1) : d248590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62258 q ha hb
    | true =>
      simp only [d25452, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25453 q = 1) (hb : d152854 q = 1) : d248591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25453, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25454 q = 1) (hb : d152854 q = 1) : d248592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25455 q = 1) (hb : d152854 q = 1) : d248593 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25455, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25691 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62232 q ha hb
    | true =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25692 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25693 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25694 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25695 q = 1) (hb : d152854 q = 1) : d248731 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25695, d248731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25695, d248731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25698 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25793 q = 1) (hb : d152855 q = 1) : d248732 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25793, d152855, d248732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25793, d152855, d248732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62260 (p : Pattern) (ha : d25799 p = 1) (hb : d152855 p = 1) : d248738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25790 q = 1) (hb : d152855 q = 1) : d248728 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25790, d248728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62257 q ha hb
    | true =>
      simp only [d25790, d248728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62231 q ha hb
  have h2 (q : Pattern) (ha : d25791 q = 1) (hb : d152855 q = 1) : d248729 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25791, d248729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25791, d248729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25792 q = 1) (hb : d152855 q = 1) : d248730 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25792, d248730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25792, d248730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25794 q = 1) (hb : d152855 q = 1) : d248733 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25794, d248733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62231 q ha hb
    | true =>
      simp only [d25794, d248733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62259 q ha hb
  have h5 (q : Pattern) (ha : d25795 q = 1) (hb : d152855 q = 1) : d248734 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25795, d248734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25795, d248734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25796 q = 1) (hb : d152855 q = 1) : d248735 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25796, d248735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25796, d248735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25797 q = 1) (hb : d152855 q = 1) : d248736 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25797, d248736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25797, d248736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25700 q = 1) (hb : d152855 q = 1) : d248674 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25700, d248674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62231 q ha hb
    | true =>
      simp only [d25700, d248674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62233 q ha hb
  have h9 (q : Pattern) (ha : d25701 q = 1) (hb : d152855 q = 1) : d248675 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25701, d248675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25701, d248675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25702 q = 1) (hb : d152855 q = 1) : d248676 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25702, d248676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25702, d248676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25704 q = 1) (hb : d152855 q = 1) : d156878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62233 q ha hb
    | true =>
      simp only [d25704, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62234 q ha hb
  have h12 (q : Pattern) (ha : d25705 q = 1) (hb : d152855 q = 1) : d156879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25706 q = 1) (hb : d152855 q = 1) : d156880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25707 q = 1) (hb : d152855 q = 1) : d248677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25707, d248677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25707, d248677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25798 q = 1) (hb : d152855 q = 1) : d248737 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25798, d248737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25798, d248737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25799 q = 1) (hb : d152855 q = 1) : d248738 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25799, d248738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25799, d248738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62261 (p : Pattern) (ha : d25805 p = 1) (hb : d152855 p = 1) : d248744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25800 q = 1) (hb : d152855 q = 1) : d248739 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25800, d248739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62260 q ha hb
    | true =>
      simp only [d25800, d248739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25801 q = 1) (hb : d152855 q = 1) : d248740 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25801, d248740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25801, d248740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25711 q = 1) (hb : d152855 q = 1) : d248680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62235 q ha hb
    | true =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25712 q = 1) (hb : d152855 q = 1) : d248681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25802 q = 1) (hb : d152855 q = 1) : d248741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25802, d248741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25802, d248741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25803 q = 1) (hb : d152855 q = 1) : d248742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25803, d248742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25803, d248742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25804 q = 1) (hb : d152855 q = 1) : d248743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25804, d248743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25804, d248743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25805 q = 1) (hb : d152855 q = 1) : d248744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25805, d248744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25805, d248744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62262 (p : Pattern) (ha : d25875 p = 1) (hb : d152855 p = 1) : d248750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d152855 q = 1) : d248680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62235 q ha hb
    | true =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d152855 q = 1) : d248681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25872 q = 1) (hb : d152855 q = 1) : d248747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25872, d248747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25872, d248747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25873 q = 1) (hb : d152855 q = 1) : d248748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25873, d248748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25873, d248748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25874 q = 1) (hb : d152855 q = 1) : d248749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25874, d248749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25874, d248749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25875 q = 1) (hb : d152855 q = 1) : d248750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25875, d248750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25875, d248750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62263 (p : Pattern) (ha : d152855 p = 1) (hb : d202094 p = 1) : d248756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25748 q = 1) (hb : d152855 q = 1) : d248706 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25748, d248706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62251 q ha hb
    | true =>
      simp only [d25748, d248706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62252 q ha hb
  have h2 (q : Pattern) (ha : d25749 q = 1) (hb : d152855 q = 1) : d248707 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25749, d248707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25749, d248707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25750 q = 1) (hb : d152855 q = 1) : d248708 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25750, d248708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25750, d248708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25751 q = 1) (hb : d152855 q = 1) : d248709 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25751, d248709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25751, d248709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25758 q = 1) (hb : d152855 q = 1) : d248713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25758, d248713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62253 q ha hb
    | true =>
      simp only [d25758, d248713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62254 q ha hb
  have h6 (q : Pattern) (ha : d25759 q = 1) (hb : d152855 q = 1) : d248714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25759, d248714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25759, d248714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25760 q = 1) (hb : d152855 q = 1) : d248715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25760, d248715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25760, d248715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25806 q = 1) (hb : d152855 q = 1) : d248745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25806, d248745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62261 q ha hb
    | true =>
      simp only [d25806, d248745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62237 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202090 q = 1) : d248746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d248746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202090, d248746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d25876 q = 1) (hb : d152855 q = 1) : d248751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25876, d248751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62262 q ha hb
    | true =>
      simp only [d25876, d248751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25877 q = 1) (hb : d152855 q = 1) : d248752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25877, d248752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25877, d248752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202091 q = 1) : d248753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d248753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202091, d248753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202092 q = 1) : d248754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d248754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202092, d248754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202093 q = 1) : d248755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d248755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202093, d248755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202094 q = 1) : d248756 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202094, d248756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202094, d248756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62264 (p : Pattern) (ha : d25882 p = 1) (hb : d152855 p = 1) : d248757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d152855 q = 1) : d248680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62235 q ha hb
    | true =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d152855 q = 1) : d248681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d152855 q = 1) : d248682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d152855 q = 1) : d248683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d248683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d248683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25744 q = 1) (hb : d152855 q = 1) : d248704 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25744, d248704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25744, d248704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25882 q = 1) (hb : d152855 q = 1) : d248757 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25882, d248757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25882, d248757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62265 (p : Pattern) (ha : d25883 p = 1) (hb : d152855 p = 1) : d156979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d152855 q = 1) : d156896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25746 q = 1) (hb : d152855 q = 1) : d156920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25746, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25746, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25883 q = 1) (hb : d152855 q = 1) : d156979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25883, d156979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25883, d156979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62266 (p : Pattern) (ha : d25888 p = 1) (hb : d152855 p = 1) : d248762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d152855 q = 1) : d248680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62235 q ha hb
    | true =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d152855 q = 1) : d248681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d152855 q = 1) : d248682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25752 q = 1) (hb : d152855 q = 1) : d248710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25752, d248710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25752, d248710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25753 q = 1) (hb : d152855 q = 1) : d248711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25753, d248711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25753, d248711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25888 q = 1) (hb : d152855 q = 1) : d248762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25888, d248762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25888, d248762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62267 (p : Pattern) (ha : d25889 p = 1) (hb : d152855 p = 1) : d156985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25755 q = 1) (hb : d152855 q = 1) : d156929 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25755, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25755, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25756 q = 1) (hb : d152855 q = 1) : d156930 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25756, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25756, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25889 q = 1) (hb : d152855 q = 1) : d156985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25889, d156985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25889, d156985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62268 (p : Pattern) (ha : d25893 p = 1) (hb : d152855 p = 1) : d248766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25800 q = 1) (hb : d152855 q = 1) : d248739 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25800, d248739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62260 q ha hb
    | true =>
      simp only [d25800, d248739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25801 q = 1) (hb : d152855 q = 1) : d248740 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25801, d248740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25801, d248740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25711 q = 1) (hb : d152855 q = 1) : d248680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62235 q ha hb
    | true =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25712 q = 1) (hb : d152855 q = 1) : d248681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25802 q = 1) (hb : d152855 q = 1) : d248741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25802, d248741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25802, d248741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25803 q = 1) (hb : d152855 q = 1) : d248742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25803, d248742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25803, d248742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25804 q = 1) (hb : d152855 q = 1) : d248743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25804, d248743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25804, d248743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25893 q = 1) (hb : d152855 q = 1) : d248766 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25893, d248766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25893, d248766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62269 (p : Pattern) (ha : d25899 p = 1) (hb : d152855 p = 1) : d248769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d152855 q = 1) : d248680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62235 q ha hb
    | true =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d152855 q = 1) : d248681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25872 q = 1) (hb : d152855 q = 1) : d248747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25872, d248747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25872, d248747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25873 q = 1) (hb : d152855 q = 1) : d248748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25873, d248748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25873, d248748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25874 q = 1) (hb : d152855 q = 1) : d248749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25874, d248749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25874, d248749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25899 q = 1) (hb : d152855 q = 1) : d248769 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25899, d248769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25899, d248769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62270 (p : Pattern) (ha : d152855 p = 1) (hb : d202099 p = 1) : d248775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25748 q = 1) (hb : d152855 q = 1) : d248706 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25748, d248706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62251 q ha hb
    | true =>
      simp only [d25748, d248706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62252 q ha hb
  have h2 (q : Pattern) (ha : d25749 q = 1) (hb : d152855 q = 1) : d248707 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25749, d248707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25749, d248707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25750 q = 1) (hb : d152855 q = 1) : d248708 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25750, d248708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25750, d248708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25751 q = 1) (hb : d152855 q = 1) : d248709 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25751, d248709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25751, d248709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25758 q = 1) (hb : d152855 q = 1) : d248713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25758, d248713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62253 q ha hb
    | true =>
      simp only [d25758, d248713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62254 q ha hb
  have h6 (q : Pattern) (ha : d25759 q = 1) (hb : d152855 q = 1) : d248714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25759, d248714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25759, d248714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25760 q = 1) (hb : d152855 q = 1) : d248715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25760, d248715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25760, d248715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25806 q = 1) (hb : d152855 q = 1) : d248745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25806, d248745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62261 q ha hb
    | true =>
      simp only [d25806, d248745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62237 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202090 q = 1) : d248746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d248746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202090, d248746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d25876 q = 1) (hb : d152855 q = 1) : d248751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25876, d248751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62262 q ha hb
    | true =>
      simp only [d25876, d248751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25877 q = 1) (hb : d152855 q = 1) : d248752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25877, d248752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25877, d248752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202091 q = 1) : d248753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d248753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202091, d248753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202092 q = 1) : d248754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d248754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202092, d248754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202093 q = 1) : d248755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d248755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202093, d248755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25884 q = 1) (hb : d152855 q = 1) : d248758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25884, d248758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62264 q ha hb
    | true =>
      simp only [d25884, d248758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62265 q ha hb
  have h16 (q : Pattern) (ha : d25885 q = 1) (hb : d152855 q = 1) : d248759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25885, d248759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25885, d248759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25886 q = 1) (hb : d152855 q = 1) : d248760 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25886, d248760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25886, d248760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25887 q = 1) (hb : d152855 q = 1) : d248761 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25887, d248761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25887, d248761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25890 q = 1) (hb : d152855 q = 1) : d248763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25890, d248763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62266 q ha hb
    | true =>
      simp only [d25890, d248763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62267 q ha hb
  have h20 (q : Pattern) (ha : d25891 q = 1) (hb : d152855 q = 1) : d248764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25891, d248764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25891, d248764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25892 q = 1) (hb : d152855 q = 1) : d248765 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25892, d248765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25892, d248765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25894 q = 1) (hb : d152855 q = 1) : d248767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25894, d248767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62268 q ha hb
    | true =>
      simp only [d25894, d248767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62240 q ha hb
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202095 q = 1) : d248768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d248768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d202095, d248768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d25900 q = 1) (hb : d152855 q = 1) : d248770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25900, d248770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62269 q ha hb
    | true =>
      simp only [d25900, d248770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25901 q = 1) (hb : d152855 q = 1) : d248771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25901, d248771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25901, d248771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d152855 q = 1) (hb : d202096 q = 1) : d248772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d248772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202096, d248772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d152855 q = 1) (hb : d202097 q = 1) : d248773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202097, d248773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d202097, d248773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d152855 q = 1) (hb : d202098 q = 1) : d248774 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202098, d248774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d202098, d248774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d152855 q = 1) (hb : d202099 q = 1) : d248775 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202099, d248775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202099, d248775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro62271 (p : Pattern) (ha : d152855 p = 1) (hb : d202106 p = 1) : d248784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25894 q = 1) (hb : d152855 q = 1) : d248767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25894, d248767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62268 q ha hb
    | true =>
      simp only [d25894, d248767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62240 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202095 q = 1) : d248768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d248768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202095, d248768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d25900 q = 1) (hb : d152855 q = 1) : d248770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25900, d248770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62269 q ha hb
    | true =>
      simp only [d25900, d248770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25901 q = 1) (hb : d152855 q = 1) : d248771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25901, d248771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25901, d248771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202096 q = 1) : d248772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d248772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202096, d248772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202104 q = 1) : d248782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202104, d248782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202104, d248782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202105 q = 1) : d248783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202105, d248783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202105, d248783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202106 q = 1) : d248784 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202106, d248784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202106, d248784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62272 (p : Pattern) (ha : d25947 p = 1) (hb : d152855 p = 1) : d248799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25933 q = 1) (hb : d152854 q = 1) : d248790 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25933, d248790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25933, d248790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62255 q ha hb
  have h2 (q : Pattern) (ha : d25771 q = 1) (hb : d152854 q = 1) : d248717 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25771, d248717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62255 q ha hb
    | true =>
      simp only [d25771, d248717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25934 q = 1) (hb : d152854 q = 1) : d248791 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25934, d248791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25934, d248791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25772 q = 1) (hb : d152854 q = 1) : d248718 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25772, d248718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25772, d248718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25935 q = 1) (hb : d152854 q = 1) : d248792 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25935, d248792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25935, d248792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25936 q = 1) (hb : d152854 q = 1) : d248793 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25936, d248793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25936, d248793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25937 q = 1) (hb : d152854 q = 1) : d248794 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25937, d248794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25937, d248794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62256 q ha hb
  have h8 (q : Pattern) (ha : d25776 q = 1) (hb : d152854 q = 1) : d248722 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25776, d248722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62256 q ha hb
    | true =>
      simp only [d25776, d248722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25938 q = 1) (hb : d152854 q = 1) : d248795 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25938, d248795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25938, d248795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25777 q = 1) (hb : d152854 q = 1) : d248723 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25777, d248723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25777, d248723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25939 q = 1) (hb : d152854 q = 1) : d248796 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25939, d248796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25939, d248796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25940 q = 1) (hb : d152854 q = 1) : d248797 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25940, d248797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25940, d248797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25941 q = 1) (hb : d152854 q = 1) : d248798 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25941, d248798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25941, d248798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25946 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25947 q = 1) (hb : d152855 q = 1) : d248799 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25947, d152855, d248799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25947, d152855, d248799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62273 (p : Pattern) (ha : d25953 p = 1) (hb : d152855 p = 1) : d248642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25577 q = 1) (hb : d152854 q = 1) : d248633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25577, d248633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25577, d248633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62204 q ha hb
  have h2 (q : Pattern) (ha : d25439 q = 1) (hb : d152854 q = 1) : d248585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d248585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62204 q ha hb
    | true =>
      simp only [d25439, d248585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25578 q = 1) (hb : d152854 q = 1) : d248634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25578, d248634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25578, d248634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25440 q = 1) (hb : d152854 q = 1) : d248586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d248586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25440, d248586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25579 q = 1) (hb : d152854 q = 1) : d248635 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25579, d248635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25579, d248635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25580 q = 1) (hb : d152854 q = 1) : d248636 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25580, d248636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25580, d248636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25581 q = 1) (hb : d152854 q = 1) : d248637 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25581, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25581, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62205 q ha hb
  have h8 (q : Pattern) (ha : d25444 q = 1) (hb : d152854 q = 1) : d248590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62205 q ha hb
    | true =>
      simp only [d25444, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25582 q = 1) (hb : d152854 q = 1) : d248638 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25582, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25582, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25445 q = 1) (hb : d152854 q = 1) : d248591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25445, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25583 q = 1) (hb : d152854 q = 1) : d248639 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25583, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25583, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25584 q = 1) (hb : d152854 q = 1) : d248640 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25584, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25584, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25585 q = 1) (hb : d152854 q = 1) : d248641 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25585, d248641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25585, d248641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25952 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25953 q = 1) (hb : d152855 q = 1) : d248642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25953, d152855, d248642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25953, d152855, d248642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62274 (p : Pattern) (ha : d25958 p = 1) (hb : d152855 p = 1) : d248804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25586 q = 1) (hb : d152854 q = 1) : d248637 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25586, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25586, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62258 q ha hb
  have h2 (q : Pattern) (ha : d25452 q = 1) (hb : d152854 q = 1) : d248590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62258 q ha hb
    | true =>
      simp only [d25452, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25587 q = 1) (hb : d152854 q = 1) : d248638 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25587, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25587, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25453 q = 1) (hb : d152854 q = 1) : d248591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25453, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25588 q = 1) (hb : d152854 q = 1) : d248639 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25588, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25588, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25589 q = 1) (hb : d152854 q = 1) : d248640 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25589, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25589, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25948 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62232 q ha hb
  have h8 (q : Pattern) (ha : d25691 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62232 q ha hb
    | true =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25949 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25692 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25950 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25951 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25952 q = 1) (hb : d152854 q = 1) : d248803 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25952, d248803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25952, d248803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25957 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25958 q = 1) (hb : d152855 q = 1) : d248804 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25958, d152855, d248804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25958, d152855, d248804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62275 (p : Pattern) (ha : d25974 p = 1) (hb : d152855 p = 1) : d248814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25954 q = 1) (hb : d152855 q = 1) : d248800 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25954, d248800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62272 q ha hb
    | true =>
      simp only [d25954, d248800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62273 q ha hb
  have h2 (q : Pattern) (ha : d25955 q = 1) (hb : d152855 q = 1) : d248801 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25955, d248801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25955, d248801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25956 q = 1) (hb : d152855 q = 1) : d248802 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25956, d248802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25956, d248802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25959 q = 1) (hb : d152855 q = 1) : d248805 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25959, d248805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62273 q ha hb
    | true =>
      simp only [d25959, d248805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62274 q ha hb
  have h5 (q : Pattern) (ha : d25960 q = 1) (hb : d152855 q = 1) : d248806 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25960, d248806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25960, d248806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25961 q = 1) (hb : d152855 q = 1) : d248807 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25961, d248807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25961, d248807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25962 q = 1) (hb : d152855 q = 1) : d248808 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25962, d248808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25962, d248808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25965 q = 1) (hb : d152855 q = 1) : d248809 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25965, d248809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62273 q ha hb
    | true =>
      simp only [d25965, d248809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62246 q ha hb
  have h9 (q : Pattern) (ha : d25966 q = 1) (hb : d152855 q = 1) : d248810 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25966, d248810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25966, d248810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25967 q = 1) (hb : d152855 q = 1) : d248811 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25967, d248811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25967, d248811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25969 q = 1) (hb : d152855 q = 1) : d157050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25969, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62246 q ha hb
    | true =>
      simp only [d25969, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62247 q ha hb
  have h12 (q : Pattern) (ha : d25970 q = 1) (hb : d152855 q = 1) : d157051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25970, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25970, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25971 q = 1) (hb : d152855 q = 1) : d157052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25971, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25971, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25972 q = 1) (hb : d152855 q = 1) : d248812 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25972, d248812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25972, d248812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25973 q = 1) (hb : d152855 q = 1) : d248813 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25973, d248813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25973, d248813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25974 q = 1) (hb : d152855 q = 1) : d248814 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25974, d248814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25974, d248814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62276 (p : Pattern) (ha : d25979 p = 1) (hb : d152855 p = 1) : d248818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25965 q = 1) (hb : d152855 q = 1) : d248809 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25965, d248809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62273 q ha hb
    | true =>
      simp only [d25965, d248809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62246 q ha hb
  have h2 (q : Pattern) (ha : d25966 q = 1) (hb : d152855 q = 1) : d248810 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25966, d248810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25966, d248810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25967 q = 1) (hb : d152855 q = 1) : d248811 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25967, d248811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25967, d248811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25969 q = 1) (hb : d152855 q = 1) : d157050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25969, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62246 q ha hb
    | true =>
      simp only [d25969, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62247 q ha hb
  have h5 (q : Pattern) (ha : d25970 q = 1) (hb : d152855 q = 1) : d157051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25970, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25970, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25971 q = 1) (hb : d152855 q = 1) : d157052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25971, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25971, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25972 q = 1) (hb : d152855 q = 1) : d248812 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25972, d248812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25972, d248812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25977 q = 1) (hb : d152855 q = 1) : d157058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25977, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25977, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25978 q = 1) (hb : d152855 q = 1) : d248817 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25978, d248817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25978, d248817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25979 q = 1) (hb : d152855 q = 1) : d248818 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25979, d248818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25979, d248818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62277 (p : Pattern) (ha : d25985 p = 1) (hb : d152855 p = 1) : d248824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25975 q = 1) (hb : d152855 q = 1) : d248815 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25975, d248815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62275 q ha hb
    | true =>
      simp only [d25975, d248815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25976 q = 1) (hb : d152855 q = 1) : d248816 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25976, d248816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25976, d248816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25980 q = 1) (hb : d152855 q = 1) : d248819 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25980, d248819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62276 q ha hb
    | true =>
      simp only [d25980, d248819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25981 q = 1) (hb : d152855 q = 1) : d248820 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25981, d248820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25981, d248820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25982 q = 1) (hb : d152855 q = 1) : d248821 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25982, d248821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25982, d248821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25983 q = 1) (hb : d152855 q = 1) : d248822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25983, d248822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25983, d248822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25984 q = 1) (hb : d152855 q = 1) : d248823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25984, d248823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25984, d248823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25985 q = 1) (hb : d152855 q = 1) : d248824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25985, d248824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25985, d248824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62278 (p : Pattern) (ha : d25993 p = 1) (hb : d152855 p = 1) : d248828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25980 q = 1) (hb : d152855 q = 1) : d248819 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25980, d248819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62276 q ha hb
    | true =>
      simp only [d25980, d248819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25981 q = 1) (hb : d152855 q = 1) : d248820 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25981, d248820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25981, d248820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25988 q = 1) (hb : d152855 q = 1) : d157069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25988, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62248 q ha hb
    | true =>
      simp only [d25988, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25989 q = 1) (hb : d152855 q = 1) : d157070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25989, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25989, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25990 q = 1) (hb : d152855 q = 1) : d248825 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25990, d248825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25990, d248825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25991 q = 1) (hb : d152855 q = 1) : d248826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25991, d248826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25991, d248826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25992 q = 1) (hb : d152855 q = 1) : d248827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25992, d248827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25992, d248827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25993 q = 1) (hb : d152855 q = 1) : d248828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25993, d248828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25993, d248828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62279 (p : Pattern) (ha : d26047 p = 1) (hb : d152855 p = 1) : d248834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25980 q = 1) (hb : d152855 q = 1) : d248819 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25980, d248819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62276 q ha hb
    | true =>
      simp only [d25980, d248819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25981 q = 1) (hb : d152855 q = 1) : d248820 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25981, d248820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25981, d248820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26044 q = 1) (hb : d152855 q = 1) : d248831 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26044, d248831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26044, d248831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26045 q = 1) (hb : d152855 q = 1) : d248832 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26045, d248832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26045, d248832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26046 q = 1) (hb : d152855 q = 1) : d248833 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26046, d248833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26046, d248833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26047 q = 1) (hb : d152855 q = 1) : d248834 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26047, d248834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26047, d248834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62280 (p : Pattern) (ha : d152855 p = 1) (hb : d202116 p = 1) : d248840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25994 q = 1) (hb : d152855 q = 1) : d248829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25994, d248829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62277 q ha hb
    | true =>
      simp only [d25994, d248829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62278 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202112 q = 1) : d248830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202112, d248830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202112, d248830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d26048 q = 1) (hb : d152855 q = 1) : d248835 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26048, d248835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62279 q ha hb
    | true =>
      simp only [d26048, d248835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26049 q = 1) (hb : d152855 q = 1) : d248836 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26049, d248836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26049, d248836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202113 q = 1) : d248837 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202113, d248837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202113, d248837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202114 q = 1) : d248838 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202114, d248838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202114, d248838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202115 q = 1) : d248839 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202115, d248839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202115, d248839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202116 q = 1) : d248840 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202116, d248840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202116, d248840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62281 (p : Pattern) (ha : d152855 p = 1) (hb : d202122 p = 1) : d248846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25731 q = 1) (hb : d152855 q = 1) : d248692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25731, d248692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25731, d248692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62239 q ha hb
  have h2 (q : Pattern) (ha : d25732 q = 1) (hb : d152855 q = 1) : d248693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25732, d248693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25732, d248693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25741 q = 1) (hb : d152855 q = 1) : d248701 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25741, d248701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62239 q ha hb
    | true =>
      simp only [d25741, d248701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62242 q ha hb
  have h4 (q : Pattern) (ha : d25742 q = 1) (hb : d152855 q = 1) : d248702 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25742, d248702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25742, d248702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25743 q = 1) (hb : d152855 q = 1) : d248703 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25743, d248703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25743, d248703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202100 q = 1) : d248776 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202100, d248776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62263 q ha hb
    | true =>
      simp only [d202100, d248776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62270 q ha hb
  have h7 (q : Pattern) (ha : d25919 q = 1) (hb : d152855 q = 1) : d248778 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25919, d248778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62243 q ha hb
    | true =>
      simp only [d25919, d248778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62244 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202101 q = 1) : d248779 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202101, d248779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202101, d248779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202102 q = 1) : d248780 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202102, d248780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202102, d248780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d202103 q = 1) : d248781 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202103, d248781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d202103, d248781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d202107 q = 1) : d248785 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202107, d248785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202107, d248785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62271 q ha hb
  have h12 (q : Pattern) (ha : d25928 q = 1) (hb : d152855 q = 1) : d157021 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25928, d157021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25928, d157021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62245 q ha hb
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202108 q = 1) : d248786 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202108, d248786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202108, d248786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202109 q = 1) : d248787 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202109, d248787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202109, d248787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202110 q = 1) : d248788 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202110, d248788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202110, d248788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d152855 q = 1) (hb : d202111 q = 1) : d248789 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202111, d248789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202111, d248789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d152855 q = 1) (hb : d202117 q = 1) : d248841 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202117, d248841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202117, d248841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62280 q ha hb
  have h18 (q : Pattern) (ha : d26065 q = 1) (hb : d152855 q = 1) : d157098 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26065, d157098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26065, d157098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62250 q ha hb
  have h19 (q : Pattern) (ha : d152855 q = 1) (hb : d202118 q = 1) : d248842 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202118, d248842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202118, d248842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d152855 q = 1) (hb : d202119 q = 1) : d248843 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202119, d248843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202119, d248843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d152855 q = 1) (hb : d202120 q = 1) : d248844 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202120, d248844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202120, d248844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d152855 q = 1) (hb : d202121 q = 1) : d248845 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202121, d248845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202121, d248845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202122 q = 1) : d248846 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202122, d248846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202122, d248846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62282 (p : Pattern) (ha : d152855 p = 1) (hb : d202128 p = 1) : d248852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202123 q = 1) : d248847 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202123, d248847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202123, d248847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62281 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202124 q = 1) : d248848 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202124, d248848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202124, d248848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202125 q = 1) : d248849 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202125, d248849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202125, d248849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202126 q = 1) : d248850 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202126, d248850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202126, d248850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202127 q = 1) : d248851 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202127, d248851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202127, d248851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202128 q = 1) : d248852 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202128, d248852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202128, d248852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62283 (p : Pattern) (ha : d26082 p = 1) (hb : d152854 p = 1) : d248855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25763 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26081 q = 1) (hb : d152852 q = 1) : d26081 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26082 q = 1) (hb : d152854 q = 1) : d248855 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26082, d152854, d248855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26082, d152854, d248855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62284 (p : Pattern) (ha : d26092 p = 1) (hb : d152854 p = 1) : d248860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26091 q = 1) (hb : d152852 q = 1) : d26091 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26092 q = 1) (hb : d152854 q = 1) : d248860 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26092, d152854, d248860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26092, d152854, d248860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62285 (p : Pattern) (ha : d26113 p = 1) (hb : d152855 p = 1) : d248866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26083 q = 1) (hb : d152854 q = 1) : d248856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26083, d248856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62283 q ha hb
    | true =>
      simp only [d26083, d248856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26084 q = 1) (hb : d152854 q = 1) : d248857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26084, d248857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26084, d248857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26085 q = 1) (hb : d152854 q = 1) : d248858 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26085, d248858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26085, d248858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26086 q = 1) (hb : d152854 q = 1) : d248859 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26086, d248859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26086, d248859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26093 q = 1) (hb : d152854 q = 1) : d248861 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26093, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62284 q ha hb
    | true =>
      simp only [d26093, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26094 q = 1) (hb : d152854 q = 1) : d248862 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26094, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26094, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26095 q = 1) (hb : d152854 q = 1) : d248863 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26095, d248863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26095, d248863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26096 q = 1) (hb : d152854 q = 1) : d248864 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26096, d248864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26096, d248864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26097 q = 1) (hb : d152854 q = 1) : d248865 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26097, d248865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26097, d248865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26112 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26113 q = 1) (hb : d152855 q = 1) : d248866 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26113, d152855, d248866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26113, d152855, d248866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62286 (p : Pattern) (ha : d26107 p = 1) (hb : d152854 p = 1) : d157124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26106 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9842 q = 1) (hb : d152852 q = 1) : d9842 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26107 q = 1) (hb : d152854 q = 1) : d157124 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26107, d152854, d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26107, d152854, d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62287 (p : Pattern) (ha : d26116 p = 1) (hb : d152854 p = 1) : d248867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26088 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26115 q = 1) (hb : d152852 q = 1) : d26115 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26116 q = 1) (hb : d152854 q = 1) : d248867 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26116, d152854, d248867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26116, d152854, d248867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62288 (p : Pattern) (ha : d26123 p = 1) (hb : d152855 p = 1) : d248873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26117 q = 1) (hb : d152854 q = 1) : d248868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26117, d248868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62287 q ha hb
    | true =>
      simp only [d26117, d248868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26118 q = 1) (hb : d152854 q = 1) : d248869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26118, d248869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26118, d248869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26119 q = 1) (hb : d152854 q = 1) : d248870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26119, d248870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26119, d248870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26120 q = 1) (hb : d152854 q = 1) : d248871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26120, d248871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26120, d248871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26108 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
    | true =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26109 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26110 q = 1) (hb : d152854 q = 1) : d157127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26110, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26110, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26111 q = 1) (hb : d152854 q = 1) : d157128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26111, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26111, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26121 q = 1) (hb : d152854 q = 1) : d248872 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26121, d248872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26121, d248872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26122 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26123 q = 1) (hb : d152855 q = 1) : d248873 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26123, d152855, d248873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26123, d152855, d248873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62289 (p : Pattern) (ha : d26127 p = 1) (hb : d152855 p = 1) : d157135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26108 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
    | true =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26109 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26110 q = 1) (hb : d152854 q = 1) : d157127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26110, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26110, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26111 q = 1) (hb : d152854 q = 1) : d157128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26111, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26111, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26122 q = 1) (hb : d152854 q = 1) : d157134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26122, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26122, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14772 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d26127 q = 1) (hb : d152855 q = 1) : d157135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26127, d152855, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26127, d152855, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62290 (p : Pattern) (ha : d26134 p = 1) (hb : d152855 p = 1) : d248883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26124 q = 1) (hb : d152855 q = 1) : d248874 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26124, d248874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62285 q ha hb
    | true =>
      simp only [d26124, d248874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62288 q ha hb
  have h2 (q : Pattern) (ha : d26125 q = 1) (hb : d152855 q = 1) : d248875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26125, d248875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26125, d248875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26126 q = 1) (hb : d152855 q = 1) : d248876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26126, d248876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26126, d248876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26128 q = 1) (hb : d152855 q = 1) : d248877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26128, d248877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62288 q ha hb
    | true =>
      simp only [d26128, d248877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62289 q ha hb
  have h5 (q : Pattern) (ha : d26129 q = 1) (hb : d152855 q = 1) : d248878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26129, d248878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26129, d248878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26130 q = 1) (hb : d152855 q = 1) : d248879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26130, d248879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26130, d248879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26131 q = 1) (hb : d152855 q = 1) : d248880 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26131, d248880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26131, d248880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26132 q = 1) (hb : d152855 q = 1) : d248881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26132, d248881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26132, d248881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26133 q = 1) (hb : d152855 q = 1) : d248882 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26133, d248882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26133, d248882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26134 q = 1) (hb : d152855 q = 1) : d248883 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26134, d248883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26134, d248883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62291 (p : Pattern) (ha : d26138 p = 1) (hb : d152855 p = 1) : d248887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26128 q = 1) (hb : d152855 q = 1) : d248877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26128, d248877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62288 q ha hb
    | true =>
      simp only [d26128, d248877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62289 q ha hb
  have h2 (q : Pattern) (ha : d26129 q = 1) (hb : d152855 q = 1) : d248878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26129, d248878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26129, d248878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26130 q = 1) (hb : d152855 q = 1) : d248879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26130, d248879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26130, d248879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26132 q = 1) (hb : d152855 q = 1) : d248881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26132, d248881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26132, d248881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26137 q = 1) (hb : d152855 q = 1) : d248886 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26137, d248886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26137, d248886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26138 q = 1) (hb : d152855 q = 1) : d248887 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26138, d248887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26138, d248887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62292 (p : Pattern) (ha : d26144 p = 1) (hb : d152855 p = 1) : d248893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d152855 q = 1) : d248884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62290 q ha hb
    | true =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d152855 q = 1) : d248885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d152855 q = 1) : d248890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26142 q = 1) (hb : d152855 q = 1) : d248891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26142, d248891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26142, d248891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26143 q = 1) (hb : d152855 q = 1) : d248892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26143, d248892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26143, d248892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26144 q = 1) (hb : d152855 q = 1) : d248893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26144, d248893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26144, d248893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62293 (p : Pattern) (ha : d26148 p = 1) (hb : d152855 p = 1) : d248897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d152855 q = 1) : d248894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26146 q = 1) (hb : d152855 q = 1) : d248895 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26146, d248895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26146, d248895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26147 q = 1) (hb : d152855 q = 1) : d248896 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26147, d248896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26147, d248896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26148 q = 1) (hb : d152855 q = 1) : d248897 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26148, d248897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26148, d248897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62294 (p : Pattern) (ha : d26154 p = 1) (hb : d152855 p = 1) : d248903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26149 q = 1) (hb : d152855 q = 1) : d248898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26149, d248898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62292 q ha hb
    | true =>
      simp only [d26149, d248898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62293 q ha hb
  have h2 (q : Pattern) (ha : d26150 q = 1) (hb : d152855 q = 1) : d248899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26150, d248899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26150, d248899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26151 q = 1) (hb : d152855 q = 1) : d248900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26151, d248900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26151, d248900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26152 q = 1) (hb : d152855 q = 1) : d248901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26152, d248901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26152, d248901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26153 q = 1) (hb : d152855 q = 1) : d248902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26153, d248902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26153, d248902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26154 q = 1) (hb : d152855 q = 1) : d248903 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26154, d248903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26154, d248903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62295 (p : Pattern) (ha : d26157 p = 1) (hb : d152855 p = 1) : d248906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d152855 q = 1) : d248884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62290 q ha hb
    | true =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d152855 q = 1) : d248885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d152855 q = 1) : d248890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26142 q = 1) (hb : d152855 q = 1) : d248891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26142, d248891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26142, d248891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26143 q = 1) (hb : d152855 q = 1) : d248892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26143, d248892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26143, d248892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26157 q = 1) (hb : d152855 q = 1) : d248906 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26157, d248906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26157, d248906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62296 (p : Pattern) (ha : d26158 p = 1) (hb : d152855 p = 1) : d248907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d152855 q = 1) : d248894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26146 q = 1) (hb : d152855 q = 1) : d248895 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26146, d248895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26146, d248895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26147 q = 1) (hb : d152855 q = 1) : d248896 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26147, d248896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26147, d248896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26158 q = 1) (hb : d152855 q = 1) : d248907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26158, d248907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26158, d248907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62297 (p : Pattern) (ha : d26164 p = 1) (hb : d152855 p = 1) : d248913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26149 q = 1) (hb : d152855 q = 1) : d248898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26149, d248898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62292 q ha hb
    | true =>
      simp only [d26149, d248898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62293 q ha hb
  have h2 (q : Pattern) (ha : d26150 q = 1) (hb : d152855 q = 1) : d248899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26150, d248899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26150, d248899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26151 q = 1) (hb : d152855 q = 1) : d248900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26151, d248900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26151, d248900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26152 q = 1) (hb : d152855 q = 1) : d248901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26152, d248901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26152, d248901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26153 q = 1) (hb : d152855 q = 1) : d248902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26153, d248902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26153, d248902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26159 q = 1) (hb : d152855 q = 1) : d248908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26159, d248908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62295 q ha hb
    | true =>
      simp only [d26159, d248908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62296 q ha hb
  have h7 (q : Pattern) (ha : d26160 q = 1) (hb : d152855 q = 1) : d248909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26160, d248909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26160, d248909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26161 q = 1) (hb : d152855 q = 1) : d248910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26161, d248910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26161, d248910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26162 q = 1) (hb : d152855 q = 1) : d248911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26162, d248911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26162, d248911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26163 q = 1) (hb : d152855 q = 1) : d248912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26163, d248912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26163, d248912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26164 q = 1) (hb : d152855 q = 1) : d248913 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26164, d248913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26164, d248913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62298 (p : Pattern) (ha : d26352 p = 1) (hb : d152855 p = 1) : d249002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26149 q = 1) (hb : d152855 q = 1) : d248898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26149, d248898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62292 q ha hb
    | true =>
      simp only [d26149, d248898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62293 q ha hb
  have h2 (q : Pattern) (ha : d26150 q = 1) (hb : d152855 q = 1) : d248899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26150, d248899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26150, d248899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26151 q = 1) (hb : d152855 q = 1) : d248900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26151, d248900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26151, d248900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26152 q = 1) (hb : d152855 q = 1) : d248901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26152, d248901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26152, d248901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26153 q = 1) (hb : d152855 q = 1) : d248902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26153, d248902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26153, d248902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26347 q = 1) (hb : d152855 q = 1) : d248997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26347, d248997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62293 q ha hb
    | true =>
      simp only [d26347, d248997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26348 q = 1) (hb : d152855 q = 1) : d248998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26348, d248998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26348, d248998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26349 q = 1) (hb : d152855 q = 1) : d248999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26349, d248999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26349, d248999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26350 q = 1) (hb : d152855 q = 1) : d249000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26350, d249000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26350, d249000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26351 q = 1) (hb : d152855 q = 1) : d249001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26351, d249001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26351, d249001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26352 q = 1) (hb : d152855 q = 1) : d249002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26352, d249002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26352, d249002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62299 (p : Pattern) (ha : d26358 p = 1) (hb : d152855 p = 1) : d249008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26347 q = 1) (hb : d152855 q = 1) : d248997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26347, d248997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62293 q ha hb
    | true =>
      simp only [d26347, d248997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26348 q = 1) (hb : d152855 q = 1) : d248998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26348, d248998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26348, d248998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26349 q = 1) (hb : d152855 q = 1) : d248999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26349, d248999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26349, d248999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26350 q = 1) (hb : d152855 q = 1) : d249000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26350, d249000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26350, d249000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26351 q = 1) (hb : d152855 q = 1) : d249001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26351, d249001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26351, d249001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26353 q = 1) (hb : d152855 q = 1) : d249003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26353, d249003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62296 q ha hb
    | true =>
      simp only [d26353, d249003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26354 q = 1) (hb : d152855 q = 1) : d249004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26354, d249004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26354, d249004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26355 q = 1) (hb : d152855 q = 1) : d249005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26355, d249005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26355, d249005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26356 q = 1) (hb : d152855 q = 1) : d249006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26356, d249006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26356, d249006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26357 q = 1) (hb : d152855 q = 1) : d249007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26357, d249007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26357, d249007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26358 q = 1) (hb : d152855 q = 1) : d249008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26358, d249008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26358, d249008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62300 (p : Pattern) (ha : d26367 p = 1) (hb : d152855 p = 1) : d249017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26353 q = 1) (hb : d152855 q = 1) : d249003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26353, d249003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62296 q ha hb
    | true =>
      simp only [d26353, d249003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26354 q = 1) (hb : d152855 q = 1) : d249004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26354, d249004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26354, d249004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26355 q = 1) (hb : d152855 q = 1) : d249005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26355, d249005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26355, d249005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26356 q = 1) (hb : d152855 q = 1) : d249006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26356, d249006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26356, d249006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26357 q = 1) (hb : d152855 q = 1) : d249007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26357, d249007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26357, d249007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26367 q = 1) (hb : d152855 q = 1) : d249017 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26367, d249017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26367, d249017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62301 (p : Pattern) (ha : d26421 p = 1) (hb : d152855 p = 1) : d249057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26416 q = 1) (hb : d152854 q = 1) : d249052 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26416, d249052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26416, d249052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62287 q ha hb
  have h2 (q : Pattern) (ha : d26117 q = 1) (hb : d152854 q = 1) : d248868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26117, d248868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62287 q ha hb
    | true =>
      simp only [d26117, d248868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26417 q = 1) (hb : d152854 q = 1) : d249053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26417, d249053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26417, d249053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26118 q = 1) (hb : d152854 q = 1) : d248869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26118, d248869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26118, d248869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26418 q = 1) (hb : d152854 q = 1) : d249054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26418, d249054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26418, d249054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26419 q = 1) (hb : d152854 q = 1) : d249055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26419, d249055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26419, d249055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26401 q = 1) (hb : d152854 q = 1) : d157314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26401, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26401, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
  have h8 (q : Pattern) (ha : d26108 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
    | true =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26402 q = 1) (hb : d152854 q = 1) : d157315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26402, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26402, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26109 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26403 q = 1) (hb : d152854 q = 1) : d157316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26403, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26403, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26404 q = 1) (hb : d152854 q = 1) : d157317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26404, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26404, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26420 q = 1) (hb : d152854 q = 1) : d249056 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26420, d249056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26420, d249056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26410 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26421 q = 1) (hb : d152855 q = 1) : d249057 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26421, d152855, d249057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26421, d152855, d249057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62302 (p : Pattern) (ha : d26425 p = 1) (hb : d152855 p = 1) : d157324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26401 q = 1) (hb : d152854 q = 1) : d157314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26401, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26401, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
  have h2 (q : Pattern) (ha : d26108 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
    | true =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26402 q = 1) (hb : d152854 q = 1) : d157315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26402, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26402, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26109 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26403 q = 1) (hb : d152854 q = 1) : d157316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26403, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26403, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26404 q = 1) (hb : d152854 q = 1) : d157317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26404, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26404, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26410 q = 1) (hb : d152854 q = 1) : d157323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26410, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26410, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15023 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d26425 q = 1) (hb : d152855 q = 1) : d157324 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26425, d152855, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26425, d152855, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62303 (p : Pattern) (ha : d26444 p = 1) (hb : d152855 p = 1) : d249079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26426 q = 1) (hb : d152855 q = 1) : d249061 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26426, d249061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62301 q ha hb
    | true =>
      simp only [d26426, d249061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62302 q ha hb
  have h2 (q : Pattern) (ha : d26427 q = 1) (hb : d152855 q = 1) : d249062 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26427, d249062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26427, d249062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26428 q = 1) (hb : d152855 q = 1) : d249063 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26428, d249063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26428, d249063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26434 q = 1) (hb : d152855 q = 1) : d249069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26434, d249069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26434, d249069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26443 q = 1) (hb : d152855 q = 1) : d249078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26443, d249078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26443, d249078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26444 q = 1) (hb : d152855 q = 1) : d249079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26444, d249079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26444, d249079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62304 (p : Pattern) (ha : d26528 p = 1) (hb : d152855 p = 1) : d249102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26445 q = 1) (hb : d152855 q = 1) : d249080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26445, d249080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62303 q ha hb
    | true =>
      simp only [d26445, d249080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26446 q = 1) (hb : d152855 q = 1) : d249081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26446, d249081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26446, d249081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26525 q = 1) (hb : d152855 q = 1) : d249099 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26525, d249099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26525, d249099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26526 q = 1) (hb : d152855 q = 1) : d249100 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26526, d249100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26526, d249100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26527 q = 1) (hb : d152855 q = 1) : d249101 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26527, d249101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26527, d249101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26528 q = 1) (hb : d152855 q = 1) : d249102 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26528, d249102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26528, d249102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62305 (p : Pattern) (ha : d26534 p = 1) (hb : d152855 p = 1) : d249108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26529 q = 1) (hb : d152855 q = 1) : d249103 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26529, d249103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62304 q ha hb
    | true =>
      simp only [d26529, d249103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26530 q = 1) (hb : d152855 q = 1) : d249104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26530, d249104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26530, d249104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26531 q = 1) (hb : d152855 q = 1) : d249105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26531, d249105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26531, d249105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26532 q = 1) (hb : d152855 q = 1) : d249106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26532, d249106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26532, d249106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26533 q = 1) (hb : d152855 q = 1) : d249107 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26533, d249107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26533, d249107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26534 q = 1) (hb : d152855 q = 1) : d249108 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26534, d249108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26534, d249108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62306 (p : Pattern) (ha : d26169 p = 1) (hb : d152855 p = 1) : d248918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d152855 q = 1) : d248884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62290 q ha hb
    | true =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d152855 q = 1) : d248885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d152855 q = 1) : d248890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26142 q = 1) (hb : d152855 q = 1) : d248891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26142, d248891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26142, d248891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26168 q = 1) (hb : d152855 q = 1) : d248917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26168, d248917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26168, d248917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26169 q = 1) (hb : d152855 q = 1) : d248918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26169, d248918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26169, d248918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62307 (p : Pattern) (ha : d26171 p = 1) (hb : d152855 p = 1) : d248920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d152855 q = 1) : d248894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26146 q = 1) (hb : d152855 q = 1) : d248895 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26146, d248895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26146, d248895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26170 q = 1) (hb : d152855 q = 1) : d248919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26170, d248919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26170, d248919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26171 q = 1) (hb : d152855 q = 1) : d248920 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26171, d248920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26171, d248920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62308 (p : Pattern) (ha : d26178 p = 1) (hb : d152855 p = 1) : d248927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d152855 q = 1) : d248884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62290 q ha hb
    | true =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d152855 q = 1) : d248885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d152855 q = 1) : d248890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26176 q = 1) (hb : d152855 q = 1) : d248925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26176, d248925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26176, d248925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26177 q = 1) (hb : d152855 q = 1) : d248926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26177, d248926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26177, d248926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26178 q = 1) (hb : d152855 q = 1) : d248927 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26178, d248927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26178, d248927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62309 (p : Pattern) (ha : d26181 p = 1) (hb : d152855 p = 1) : d248930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d152855 q = 1) : d248894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26179 q = 1) (hb : d152855 q = 1) : d248928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26179, d248928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26179, d248928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26180 q = 1) (hb : d152855 q = 1) : d248929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26180, d248929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26180, d248929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26181 q = 1) (hb : d152855 q = 1) : d248930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26181, d248930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26181, d248930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62310 (p : Pattern) (ha : d26188 p = 1) (hb : d152854 p = 1) : d248934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26187 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9761 q = 1) (hb : d152852 q = 1) : d9761 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26188 q = 1) (hb : d152854 q = 1) : d248934 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26188, d152854, d248934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26188, d152854, d248934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62311 (p : Pattern) (ha : d26193 p = 1) (hb : d152854 p = 1) : d248939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25763 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26099 q = 1) (hb : d152852 q = 1) : d26099 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26193 q = 1) (hb : d152854 q = 1) : d248939 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26193, d152854, d248939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26193, d152854, d248939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62312 (p : Pattern) (ha : d26205 p = 1) (hb : d152855 p = 1) : d248945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26189 q = 1) (hb : d152854 q = 1) : d248935 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26189, d248935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62310 q ha hb
    | true =>
      simp only [d26189, d248935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26190 q = 1) (hb : d152854 q = 1) : d248936 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26190, d248936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26190, d248936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26191 q = 1) (hb : d152854 q = 1) : d248937 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26191, d248937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26191, d248937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26192 q = 1) (hb : d152854 q = 1) : d248938 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26192, d248938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26192, d248938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26194 q = 1) (hb : d152854 q = 1) : d248940 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26194, d248940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62311 q ha hb
    | true =>
      simp only [d26194, d248940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26195 q = 1) (hb : d152854 q = 1) : d248941 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26195, d248941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26195, d248941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26196 q = 1) (hb : d152854 q = 1) : d248942 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26196, d248942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26196, d248942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26197 q = 1) (hb : d152854 q = 1) : d248943 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26197, d248943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26197, d248943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26198 q = 1) (hb : d152854 q = 1) : d248944 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26198, d248944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26198, d248944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26204 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26205 q = 1) (hb : d152855 q = 1) : d248945 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26205, d152855, d248945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26205, d152855, d248945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62313 (p : Pattern) (ha : d26100 p = 1) (hb : d152854 p = 1) : d248860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26091 q = 1) (hb : d152852 q = 1) : d26091 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26100 q = 1) (hb : d152854 q = 1) : d248860 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26100, d152854, d248860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26100, d152854, d248860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62314 (p : Pattern) (ha : d26209 p = 1) (hb : d152855 p = 1) : d248950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26101 q = 1) (hb : d152854 q = 1) : d248861 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26101, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62313 q ha hb
    | true =>
      simp only [d26101, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26102 q = 1) (hb : d152854 q = 1) : d248862 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26102, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26102, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26103 q = 1) (hb : d152854 q = 1) : d248863 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26103, d248863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26103, d248863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26104 q = 1) (hb : d152854 q = 1) : d248864 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26104, d248864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26104, d248864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26108 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
    | true =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26109 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26110 q = 1) (hb : d152854 q = 1) : d157127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26110, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26110, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26111 q = 1) (hb : d152854 q = 1) : d157128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26111, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26111, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26112 q = 1) (hb : d152854 q = 1) : d248949 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26112, d248949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26112, d248949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26122 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26209 q = 1) (hb : d152855 q = 1) : d248950 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26209, d152855, d248950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26209, d152855, d248950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62315 (p : Pattern) (ha : d26215 p = 1) (hb : d152855 p = 1) : d248956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26206 q = 1) (hb : d152855 q = 1) : d248946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26206, d248946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62312 q ha hb
    | true =>
      simp only [d26206, d248946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62285 q ha hb
  have h2 (q : Pattern) (ha : d26207 q = 1) (hb : d152855 q = 1) : d248947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26207, d248947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26207, d248947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26208 q = 1) (hb : d152855 q = 1) : d248948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26208, d248948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26208, d248948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26210 q = 1) (hb : d152855 q = 1) : d248951 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26210, d248951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62285 q ha hb
    | true =>
      simp only [d26210, d248951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62314 q ha hb
  have h5 (q : Pattern) (ha : d26211 q = 1) (hb : d152855 q = 1) : d248952 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26211, d248952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26211, d248952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26212 q = 1) (hb : d152855 q = 1) : d248953 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26212, d248953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26212, d248953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26213 q = 1) (hb : d152855 q = 1) : d248954 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26213, d248954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26213, d248954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26124 q = 1) (hb : d152855 q = 1) : d248874 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26124, d248874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62285 q ha hb
    | true =>
      simp only [d26124, d248874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62288 q ha hb
  have h9 (q : Pattern) (ha : d26125 q = 1) (hb : d152855 q = 1) : d248875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26125, d248875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26125, d248875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26126 q = 1) (hb : d152855 q = 1) : d248876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26126, d248876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26126, d248876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26128 q = 1) (hb : d152855 q = 1) : d248877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26128, d248877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62288 q ha hb
    | true =>
      simp only [d26128, d248877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62289 q ha hb
  have h12 (q : Pattern) (ha : d26129 q = 1) (hb : d152855 q = 1) : d248878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26129, d248878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26129, d248878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26130 q = 1) (hb : d152855 q = 1) : d248879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26130, d248879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26130, d248879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26131 q = 1) (hb : d152855 q = 1) : d248880 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26131, d248880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26131, d248880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26214 q = 1) (hb : d152855 q = 1) : d248955 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26214, d248955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26214, d248955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d26215 q = 1) (hb : d152855 q = 1) : d248956 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26215, d248956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26215, d248956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62316 (p : Pattern) (ha : d26221 p = 1) (hb : d152855 p = 1) : d248962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26216 q = 1) (hb : d152855 q = 1) : d248957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26216, d248957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62315 q ha hb
    | true =>
      simp only [d26216, d248957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26217 q = 1) (hb : d152855 q = 1) : d248958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26217, d248958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26217, d248958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26135 q = 1) (hb : d152855 q = 1) : d248884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62290 q ha hb
    | true =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26136 q = 1) (hb : d152855 q = 1) : d248885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26218 q = 1) (hb : d152855 q = 1) : d248959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26218, d248959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26218, d248959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26219 q = 1) (hb : d152855 q = 1) : d248960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26219, d248960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26219, d248960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26220 q = 1) (hb : d152855 q = 1) : d248961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26220, d248961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26220, d248961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26221 q = 1) (hb : d152855 q = 1) : d248962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26221, d248962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26221, d248962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62317 (p : Pattern) (ha : d26303 p = 1) (hb : d152855 p = 1) : d157135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26108 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
    | true =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26109 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26110 q = 1) (hb : d152854 q = 1) : d157127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26110, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26110, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26111 q = 1) (hb : d152854 q = 1) : d157128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26111, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26111, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26122 q = 1) (hb : d152854 q = 1) : d157134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26122, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26122, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d26303 q = 1) (hb : d152855 q = 1) : d157135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26303, d152855, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26303, d152855, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62318 (p : Pattern) (ha : d26309 p = 1) (hb : d152855 p = 1) : d248883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26124 q = 1) (hb : d152855 q = 1) : d248874 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26124, d248874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62285 q ha hb
    | true =>
      simp only [d26124, d248874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62288 q ha hb
  have h2 (q : Pattern) (ha : d26125 q = 1) (hb : d152855 q = 1) : d248875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26125, d248875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26125, d248875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26126 q = 1) (hb : d152855 q = 1) : d248876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26126, d248876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26126, d248876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26128 q = 1) (hb : d152855 q = 1) : d248877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26128, d248877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62288 q ha hb
    | true =>
      simp only [d26128, d248877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62289 q ha hb
  have h5 (q : Pattern) (ha : d26129 q = 1) (hb : d152855 q = 1) : d248878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26129, d248878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26129, d248878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26130 q = 1) (hb : d152855 q = 1) : d248879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26130, d248879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26130, d248879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26131 q = 1) (hb : d152855 q = 1) : d248880 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26131, d248880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26131, d248880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26304 q = 1) (hb : d152855 q = 1) : d248877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26304, d248877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62288 q ha hb
    | true =>
      simp only [d26304, d248877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62317 q ha hb
  have h9 (q : Pattern) (ha : d26305 q = 1) (hb : d152855 q = 1) : d248878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26305, d248878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26305, d248878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26306 q = 1) (hb : d152855 q = 1) : d248879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26306, d248879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26306, d248879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26307 q = 1) (hb : d152855 q = 1) : d248881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26307, d248881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26307, d248881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26308 q = 1) (hb : d152855 q = 1) : d248882 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26308, d248882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26308, d248882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26309 q = 1) (hb : d152855 q = 1) : d248883 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26309, d248883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26309, d248883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro62319 (p : Pattern) (ha : d26315 p = 1) (hb : d152855 p = 1) : d248968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26310 q = 1) (hb : d152855 q = 1) : d248884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26310, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62318 q ha hb
    | true =>
      simp only [d26310, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26311 q = 1) (hb : d152855 q = 1) : d248885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26311, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26311, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26312 q = 1) (hb : d152855 q = 1) : d248965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26312, d248965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26312, d248965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26313 q = 1) (hb : d152855 q = 1) : d248966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26313, d248966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26313, d248966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26314 q = 1) (hb : d152855 q = 1) : d248967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26314, d248967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26314, d248967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26315 q = 1) (hb : d152855 q = 1) : d248968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26315, d248968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26315, d248968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62320 (p : Pattern) (ha : d152855 p = 1) (hb : d202135 p = 1) : d248974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26172 q = 1) (hb : d152855 q = 1) : d248921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26172, d248921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62306 q ha hb
    | true =>
      simp only [d26172, d248921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62307 q ha hb
  have h2 (q : Pattern) (ha : d26173 q = 1) (hb : d152855 q = 1) : d248922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26173, d248922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26173, d248922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26174 q = 1) (hb : d152855 q = 1) : d248923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26174, d248923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26174, d248923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26175 q = 1) (hb : d152855 q = 1) : d248924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26175, d248924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26175, d248924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26182 q = 1) (hb : d152855 q = 1) : d248931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26182, d248931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62308 q ha hb
    | true =>
      simp only [d26182, d248931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62309 q ha hb
  have h6 (q : Pattern) (ha : d26183 q = 1) (hb : d152855 q = 1) : d248932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26183, d248932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26183, d248932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26184 q = 1) (hb : d152855 q = 1) : d248933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26184, d248933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26184, d248933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26222 q = 1) (hb : d152855 q = 1) : d248963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26222, d248963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62316 q ha hb
    | true =>
      simp only [d26222, d248963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62292 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202131 q = 1) : d248964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202131, d248964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202131, d248964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d26316 q = 1) (hb : d152855 q = 1) : d248969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26316, d248969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62319 q ha hb
    | true =>
      simp only [d26316, d248969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26317 q = 1) (hb : d152855 q = 1) : d248970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26317, d248970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26317, d248970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202132 q = 1) : d248971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202132, d248971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202132, d248971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202133 q = 1) : d248972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202133, d248972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202133, d248972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202134 q = 1) : d248973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202134, d248973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202134, d248973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202135 q = 1) : d248974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202135, d248974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202135, d248974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62321 (p : Pattern) (ha : d26322 p = 1) (hb : d152855 p = 1) : d248975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d152855 q = 1) : d248884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62290 q ha hb
    | true =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d152855 q = 1) : d248885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d152855 q = 1) : d248890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26142 q = 1) (hb : d152855 q = 1) : d248891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26142, d248891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26142, d248891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26168 q = 1) (hb : d152855 q = 1) : d248917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26168, d248917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26168, d248917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26322 q = 1) (hb : d152855 q = 1) : d248975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26322, d248975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26322, d248975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62322 (p : Pattern) (ha : d26323 p = 1) (hb : d152855 p = 1) : d248976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d152855 q = 1) : d248894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26146 q = 1) (hb : d152855 q = 1) : d248895 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26146, d248895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26146, d248895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26170 q = 1) (hb : d152855 q = 1) : d248919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26170, d248919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26170, d248919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26323 q = 1) (hb : d152855 q = 1) : d248976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26323, d248976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26323, d248976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62323 (p : Pattern) (ha : d26328 p = 1) (hb : d152855 p = 1) : d248981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d152855 q = 1) : d248884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62290 q ha hb
    | true =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d152855 q = 1) : d248885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d152855 q = 1) : d248890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d248890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26176 q = 1) (hb : d152855 q = 1) : d248925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26176, d248925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26176, d248925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26177 q = 1) (hb : d152855 q = 1) : d248926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26177, d248926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26177, d248926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26328 q = 1) (hb : d152855 q = 1) : d248981 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26328, d248981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26328, d248981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62324 (p : Pattern) (ha : d26329 p = 1) (hb : d152855 p = 1) : d248982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d152855 q = 1) : d248888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62291 q ha hb
    | true =>
      simp only [d26139, d248888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d152855 q = 1) : d248889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d248889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d152855 q = 1) : d248894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d248894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26179 q = 1) (hb : d152855 q = 1) : d248928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26179, d248928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26179, d248928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26180 q = 1) (hb : d152855 q = 1) : d248929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26180, d248929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26180, d248929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26329 q = 1) (hb : d152855 q = 1) : d248982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26329, d248982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26329, d248982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62325 (p : Pattern) (ha : d26333 p = 1) (hb : d152855 p = 1) : d248986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26216 q = 1) (hb : d152855 q = 1) : d248957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26216, d248957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62315 q ha hb
    | true =>
      simp only [d26216, d248957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26217 q = 1) (hb : d152855 q = 1) : d248958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26217, d248958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26217, d248958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26135 q = 1) (hb : d152855 q = 1) : d248884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62290 q ha hb
    | true =>
      simp only [d26135, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26136 q = 1) (hb : d152855 q = 1) : d248885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26218 q = 1) (hb : d152855 q = 1) : d248959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26218, d248959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26218, d248959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26219 q = 1) (hb : d152855 q = 1) : d248960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26219, d248960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26219, d248960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26220 q = 1) (hb : d152855 q = 1) : d248961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26220, d248961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26220, d248961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26333 q = 1) (hb : d152855 q = 1) : d248986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26333, d248986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26333, d248986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62326 (p : Pattern) (ha : d26339 p = 1) (hb : d152855 p = 1) : d248989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26310 q = 1) (hb : d152855 q = 1) : d248884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26310, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62318 q ha hb
    | true =>
      simp only [d26310, d248884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26311 q = 1) (hb : d152855 q = 1) : d248885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26311, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26311, d248885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26312 q = 1) (hb : d152855 q = 1) : d248965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26312, d248965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26312, d248965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26313 q = 1) (hb : d152855 q = 1) : d248966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26313, d248966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26313, d248966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26314 q = 1) (hb : d152855 q = 1) : d248967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26314, d248967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26314, d248967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26339 q = 1) (hb : d152855 q = 1) : d248989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26339, d248989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26339, d248989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62327 (p : Pattern) (ha : d152855 p = 1) (hb : d202140 p = 1) : d248995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26172 q = 1) (hb : d152855 q = 1) : d248921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26172, d248921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62306 q ha hb
    | true =>
      simp only [d26172, d248921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62307 q ha hb
  have h2 (q : Pattern) (ha : d26173 q = 1) (hb : d152855 q = 1) : d248922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26173, d248922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26173, d248922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26174 q = 1) (hb : d152855 q = 1) : d248923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26174, d248923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26174, d248923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26175 q = 1) (hb : d152855 q = 1) : d248924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26175, d248924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26175, d248924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26182 q = 1) (hb : d152855 q = 1) : d248931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26182, d248931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62308 q ha hb
    | true =>
      simp only [d26182, d248931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62309 q ha hb
  have h6 (q : Pattern) (ha : d26183 q = 1) (hb : d152855 q = 1) : d248932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26183, d248932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26183, d248932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26184 q = 1) (hb : d152855 q = 1) : d248933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26184, d248933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26184, d248933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26222 q = 1) (hb : d152855 q = 1) : d248963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26222, d248963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62316 q ha hb
    | true =>
      simp only [d26222, d248963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62292 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202131 q = 1) : d248964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202131, d248964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202131, d248964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d26316 q = 1) (hb : d152855 q = 1) : d248969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26316, d248969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62319 q ha hb
    | true =>
      simp only [d26316, d248969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26317 q = 1) (hb : d152855 q = 1) : d248970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26317, d248970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26317, d248970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202132 q = 1) : d248971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202132, d248971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202132, d248971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202133 q = 1) : d248972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202133, d248972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202133, d248972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202134 q = 1) : d248973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202134, d248973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202134, d248973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26324 q = 1) (hb : d152855 q = 1) : d248977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26324, d248977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62321 q ha hb
    | true =>
      simp only [d26324, d248977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62322 q ha hb
  have h16 (q : Pattern) (ha : d26325 q = 1) (hb : d152855 q = 1) : d248978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26325, d248978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26325, d248978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d26326 q = 1) (hb : d152855 q = 1) : d248979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26326, d248979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d26326, d248979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d26327 q = 1) (hb : d152855 q = 1) : d248980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26327, d248980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26327, d248980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d26330 q = 1) (hb : d152855 q = 1) : d248983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26330, d248983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62323 q ha hb
    | true =>
      simp only [d26330, d248983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62324 q ha hb
  have h20 (q : Pattern) (ha : d26331 q = 1) (hb : d152855 q = 1) : d248984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26331, d248984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26331, d248984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d26332 q = 1) (hb : d152855 q = 1) : d248985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26332, d248985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d26332, d248985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d26334 q = 1) (hb : d152855 q = 1) : d248987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26334, d248987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62325 q ha hb
    | true =>
      simp only [d26334, d248987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62295 q ha hb
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202136 q = 1) : d248988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202136, d248988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d202136, d248988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d26340 q = 1) (hb : d152855 q = 1) : d248990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26340, d248990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62326 q ha hb
    | true =>
      simp only [d26340, d248990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d26341 q = 1) (hb : d152855 q = 1) : d248991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26341, d248991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d26341, d248991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d152855 q = 1) (hb : d202137 q = 1) : d248992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202137, d248992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202137, d248992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d152855 q = 1) (hb : d202138 q = 1) : d248993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202138, d248993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d202138, d248993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d152855 q = 1) (hb : d202139 q = 1) : d248994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202139, d248994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d202139, d248994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d152855 q = 1) (hb : d202140 q = 1) : d248995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202140, d248995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202140, d248995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro62328 (p : Pattern) (ha : d152855 p = 1) (hb : d202147 p = 1) : d249015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26334 q = 1) (hb : d152855 q = 1) : d248987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26334, d248987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62325 q ha hb
    | true =>
      simp only [d26334, d248987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62295 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202136 q = 1) : d248988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202136, d248988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202136, d248988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d26340 q = 1) (hb : d152855 q = 1) : d248990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26340, d248990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62326 q ha hb
    | true =>
      simp only [d26340, d248990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26341 q = 1) (hb : d152855 q = 1) : d248991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26341, d248991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26341, d248991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202137 q = 1) : d248992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202137, d248992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202137, d248992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202145 q = 1) : d249013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202145, d249013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202145, d249013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202146 q = 1) : d249014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202146, d249014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202146, d249014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202147 q = 1) : d249015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202147, d249015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202147, d249015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62329 (p : Pattern) (ha : d26391 p = 1) (hb : d152855 p = 1) : d249032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26373 q = 1) (hb : d152854 q = 1) : d249023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26373, d249023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26373, d249023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62310 q ha hb
  have h2 (q : Pattern) (ha : d26189 q = 1) (hb : d152854 q = 1) : d248935 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26189, d248935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62310 q ha hb
    | true =>
      simp only [d26189, d248935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26374 q = 1) (hb : d152854 q = 1) : d249024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26374, d249024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26374, d249024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26190 q = 1) (hb : d152854 q = 1) : d248936 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26190, d248936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26190, d248936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26375 q = 1) (hb : d152854 q = 1) : d249025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26375, d249025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26375, d249025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26376 q = 1) (hb : d152854 q = 1) : d249026 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26376, d249026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26376, d249026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26377 q = 1) (hb : d152854 q = 1) : d249027 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26377, d249027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26377, d249027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62311 q ha hb
  have h8 (q : Pattern) (ha : d26194 q = 1) (hb : d152854 q = 1) : d248940 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26194, d248940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62311 q ha hb
    | true =>
      simp only [d26194, d248940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26378 q = 1) (hb : d152854 q = 1) : d249028 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26378, d249028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26378, d249028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26195 q = 1) (hb : d152854 q = 1) : d248941 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26195, d248941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26195, d248941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26379 q = 1) (hb : d152854 q = 1) : d249029 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26379, d249029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26379, d249029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26380 q = 1) (hb : d152854 q = 1) : d249030 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26380, d249030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26380, d249030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26381 q = 1) (hb : d152854 q = 1) : d249031 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26381, d249031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26381, d249031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26390 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26391 q = 1) (hb : d152855 q = 1) : d249032 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26391, d152855, d249032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26391, d152855, d249032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62330 (p : Pattern) (ha : d26406 p = 1) (hb : d152855 p = 1) : d249042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26392 q = 1) (hb : d152854 q = 1) : d249033 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26392, d249033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26392, d249033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62283 q ha hb
  have h2 (q : Pattern) (ha : d26083 q = 1) (hb : d152854 q = 1) : d248856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26083, d248856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62283 q ha hb
    | true =>
      simp only [d26083, d248856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26393 q = 1) (hb : d152854 q = 1) : d249034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26393, d249034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26393, d249034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26084 q = 1) (hb : d152854 q = 1) : d248857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26084, d248857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26084, d248857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26394 q = 1) (hb : d152854 q = 1) : d249035 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26394, d249035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26394, d249035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26395 q = 1) (hb : d152854 q = 1) : d249036 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26395, d249036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26395, d249036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26396 q = 1) (hb : d152854 q = 1) : d249037 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26396, d249037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26396, d249037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62284 q ha hb
  have h8 (q : Pattern) (ha : d26093 q = 1) (hb : d152854 q = 1) : d248861 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26093, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62284 q ha hb
    | true =>
      simp only [d26093, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26397 q = 1) (hb : d152854 q = 1) : d249038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26397, d249038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26397, d249038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26094 q = 1) (hb : d152854 q = 1) : d248862 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26094, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26094, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26398 q = 1) (hb : d152854 q = 1) : d249039 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26398, d249039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26398, d249039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26399 q = 1) (hb : d152854 q = 1) : d249040 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26399, d249040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26399, d249040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26400 q = 1) (hb : d152854 q = 1) : d249041 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26400, d249041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26400, d249041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26405 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26406 q = 1) (hb : d152855 q = 1) : d249042 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26406, d152855, d249042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26406, d152855, d249042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62331 (p : Pattern) (ha : d26411 p = 1) (hb : d152855 p = 1) : d249047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26386 q = 1) (hb : d152854 q = 1) : d249037 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26386, d249037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26386, d249037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62313 q ha hb
  have h2 (q : Pattern) (ha : d26101 q = 1) (hb : d152854 q = 1) : d248861 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26101, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62313 q ha hb
    | true =>
      simp only [d26101, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26387 q = 1) (hb : d152854 q = 1) : d249038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26387, d249038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26387, d249038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26102 q = 1) (hb : d152854 q = 1) : d248862 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26102, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26102, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26388 q = 1) (hb : d152854 q = 1) : d249039 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26388, d249039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26388, d249039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26389 q = 1) (hb : d152854 q = 1) : d249040 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26389, d249040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26389, d249040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26401 q = 1) (hb : d152854 q = 1) : d157314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26401, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26401, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
  have h8 (q : Pattern) (ha : d26108 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
    | true =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26402 q = 1) (hb : d152854 q = 1) : d157315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26402, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26402, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26109 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26403 q = 1) (hb : d152854 q = 1) : d157316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26403, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26403, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26404 q = 1) (hb : d152854 q = 1) : d157317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26404, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26404, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26405 q = 1) (hb : d152854 q = 1) : d249046 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26405, d249046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26405, d249046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26410 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26411 q = 1) (hb : d152855 q = 1) : d249047 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26411, d152855, d249047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26411, d152855, d249047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62332 (p : Pattern) (ha : d26431 p = 1) (hb : d152855 p = 1) : d249066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26407 q = 1) (hb : d152855 q = 1) : d249043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26407, d249043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62329 q ha hb
    | true =>
      simp only [d26407, d249043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62330 q ha hb
  have h2 (q : Pattern) (ha : d26408 q = 1) (hb : d152855 q = 1) : d249044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26408, d249044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26408, d249044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26409 q = 1) (hb : d152855 q = 1) : d249045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26409, d249045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26409, d249045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26412 q = 1) (hb : d152855 q = 1) : d249048 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26412, d249048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62330 q ha hb
    | true =>
      simp only [d26412, d249048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62331 q ha hb
  have h5 (q : Pattern) (ha : d26413 q = 1) (hb : d152855 q = 1) : d249049 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26413, d249049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26413, d249049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26414 q = 1) (hb : d152855 q = 1) : d249050 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26414, d249050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26414, d249050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26415 q = 1) (hb : d152855 q = 1) : d249051 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26415, d249051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26415, d249051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26422 q = 1) (hb : d152855 q = 1) : d249058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26422, d249058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62330 q ha hb
    | true =>
      simp only [d26422, d249058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62301 q ha hb
  have h9 (q : Pattern) (ha : d26423 q = 1) (hb : d152855 q = 1) : d249059 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26423, d249059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26423, d249059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26424 q = 1) (hb : d152855 q = 1) : d249060 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26424, d249060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26424, d249060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26426 q = 1) (hb : d152855 q = 1) : d249061 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26426, d249061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62301 q ha hb
    | true =>
      simp only [d26426, d249061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62302 q ha hb
  have h12 (q : Pattern) (ha : d26427 q = 1) (hb : d152855 q = 1) : d249062 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26427, d249062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26427, d249062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26428 q = 1) (hb : d152855 q = 1) : d249063 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26428, d249063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26428, d249063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26429 q = 1) (hb : d152855 q = 1) : d249064 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26429, d249064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26429, d249064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26430 q = 1) (hb : d152855 q = 1) : d249065 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26430, d249065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26430, d249065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d26431 q = 1) (hb : d152855 q = 1) : d249066 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26431, d249066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26431, d249066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62333 (p : Pattern) (ha : d26436 p = 1) (hb : d152855 p = 1) : d249071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26422 q = 1) (hb : d152855 q = 1) : d249058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26422, d249058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62330 q ha hb
    | true =>
      simp only [d26422, d249058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62301 q ha hb
  have h2 (q : Pattern) (ha : d26423 q = 1) (hb : d152855 q = 1) : d249059 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26423, d249059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26423, d249059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26424 q = 1) (hb : d152855 q = 1) : d249060 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26424, d249060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26424, d249060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26426 q = 1) (hb : d152855 q = 1) : d249061 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26426, d249061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62301 q ha hb
    | true =>
      simp only [d26426, d249061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62302 q ha hb
  have h5 (q : Pattern) (ha : d26427 q = 1) (hb : d152855 q = 1) : d249062 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26427, d249062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26427, d249062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26428 q = 1) (hb : d152855 q = 1) : d249063 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26428, d249063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26428, d249063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26429 q = 1) (hb : d152855 q = 1) : d249064 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26429, d249064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26429, d249064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26434 q = 1) (hb : d152855 q = 1) : d249069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26434, d249069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26434, d249069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26435 q = 1) (hb : d152855 q = 1) : d249070 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26435, d249070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26435, d249070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26436 q = 1) (hb : d152855 q = 1) : d249071 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26436, d249071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26436, d249071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62334 (p : Pattern) (ha : d26442 p = 1) (hb : d152855 p = 1) : d249077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26432 q = 1) (hb : d152855 q = 1) : d249067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26432, d249067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62332 q ha hb
    | true =>
      simp only [d26432, d249067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26433 q = 1) (hb : d152855 q = 1) : d249068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26433, d249068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26433, d249068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26437 q = 1) (hb : d152855 q = 1) : d249072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26437, d249072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62333 q ha hb
    | true =>
      simp only [d26437, d249072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26438 q = 1) (hb : d152855 q = 1) : d249073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26438, d249073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26438, d249073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26439 q = 1) (hb : d152855 q = 1) : d249074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26439, d249074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26439, d249074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26440 q = 1) (hb : d152855 q = 1) : d249075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26440, d249075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26440, d249075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26441 q = 1) (hb : d152855 q = 1) : d249076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26441, d249076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26441, d249076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26442 q = 1) (hb : d152855 q = 1) : d249077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26442, d249077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26442, d249077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62335 (p : Pattern) (ha : d26450 p = 1) (hb : d152855 p = 1) : d249085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26437 q = 1) (hb : d152855 q = 1) : d249072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26437, d249072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62333 q ha hb
    | true =>
      simp only [d26437, d249072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26438 q = 1) (hb : d152855 q = 1) : d249073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26438, d249073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26438, d249073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26445 q = 1) (hb : d152855 q = 1) : d249080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26445, d249080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62303 q ha hb
    | true =>
      simp only [d26445, d249080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26446 q = 1) (hb : d152855 q = 1) : d249081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26446, d249081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26446, d249081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26447 q = 1) (hb : d152855 q = 1) : d249082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26447, d249082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26447, d249082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26448 q = 1) (hb : d152855 q = 1) : d249083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26448, d249083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26448, d249083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26449 q = 1) (hb : d152855 q = 1) : d249084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26449, d249084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26449, d249084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26450 q = 1) (hb : d152855 q = 1) : d249085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26450, d249085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26450, d249085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62336 (p : Pattern) (ha : d26505 p = 1) (hb : d152855 p = 1) : d157324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26401 q = 1) (hb : d152854 q = 1) : d157314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26401, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26401, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
  have h2 (q : Pattern) (ha : d26108 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62286 q ha hb
    | true =>
      simp only [d26108, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26402 q = 1) (hb : d152854 q = 1) : d157315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26402, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26402, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26109 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26109, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26403 q = 1) (hb : d152854 q = 1) : d157316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26403, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26403, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26404 q = 1) (hb : d152854 q = 1) : d157317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26404, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26404, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26410 q = 1) (hb : d152854 q = 1) : d157323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26410, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26410, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d26505 q = 1) (hb : d152855 q = 1) : d157324 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26505, d152855, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26505, d152855, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62337 (p : Pattern) (ha : d26511 p = 1) (hb : d152855 p = 1) : d249071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26422 q = 1) (hb : d152855 q = 1) : d249058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26422, d249058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62330 q ha hb
    | true =>
      simp only [d26422, d249058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62301 q ha hb
  have h2 (q : Pattern) (ha : d26423 q = 1) (hb : d152855 q = 1) : d249059 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26423, d249059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26423, d249059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26424 q = 1) (hb : d152855 q = 1) : d249060 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26424, d249060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26424, d249060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26426 q = 1) (hb : d152855 q = 1) : d249061 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26426, d249061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62301 q ha hb
    | true =>
      simp only [d26426, d249061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62302 q ha hb
  have h5 (q : Pattern) (ha : d26427 q = 1) (hb : d152855 q = 1) : d249062 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26427, d249062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26427, d249062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26428 q = 1) (hb : d152855 q = 1) : d249063 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26428, d249063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26428, d249063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26429 q = 1) (hb : d152855 q = 1) : d249064 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26429, d249064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26429, d249064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26506 q = 1) (hb : d152855 q = 1) : d249061 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26506, d249061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62301 q ha hb
    | true =>
      simp only [d26506, d249061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62336 q ha hb
  have h9 (q : Pattern) (ha : d26507 q = 1) (hb : d152855 q = 1) : d249062 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26507, d249062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26507, d249062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26508 q = 1) (hb : d152855 q = 1) : d249063 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26508, d249063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26508, d249063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26509 q = 1) (hb : d152855 q = 1) : d249069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26509, d249069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26509, d249069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26510 q = 1) (hb : d152855 q = 1) : d249070 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26510, d249070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26510, d249070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26511 q = 1) (hb : d152855 q = 1) : d249071 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26511, d249071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26511, d249071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro62338 (p : Pattern) (ha : d26517 p = 1) (hb : d152855 p = 1) : d249091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26512 q = 1) (hb : d152855 q = 1) : d249072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26512, d249072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62337 q ha hb
    | true =>
      simp only [d26512, d249072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26513 q = 1) (hb : d152855 q = 1) : d249073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26513, d249073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26513, d249073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26514 q = 1) (hb : d152855 q = 1) : d249088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26514, d249088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26514, d249088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26515 q = 1) (hb : d152855 q = 1) : d249089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26515, d249089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26515, d249089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26516 q = 1) (hb : d152855 q = 1) : d249090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26516, d249090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26516, d249090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26517 q = 1) (hb : d152855 q = 1) : d249091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26517, d249091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26517, d249091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62339 (p : Pattern) (ha : d152855 p = 1) (hb : d202157 p = 1) : d249097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26451 q = 1) (hb : d152855 q = 1) : d249086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26451, d249086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62334 q ha hb
    | true =>
      simp only [d26451, d249086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62335 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202153 q = 1) : d249087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202153, d249087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202153, d249087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d26518 q = 1) (hb : d152855 q = 1) : d249092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26518, d249092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62338 q ha hb
    | true =>
      simp only [d26518, d249092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26519 q = 1) (hb : d152855 q = 1) : d249093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26519, d249093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26519, d249093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202154 q = 1) : d249094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202154, d249094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202154, d249094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202155 q = 1) : d249095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202155, d249095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202155, d249095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202156 q = 1) : d249096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202156, d249096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202156, d249096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202157 q = 1) : d249097 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202157, d249097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202157, d249097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62340 (p : Pattern) (ha : d152855 p = 1) (hb : d202163 p = 1) : d249114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26155 q = 1) (hb : d152855 q = 1) : d248904 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26155, d248904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26155, d248904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62294 q ha hb
  have h2 (q : Pattern) (ha : d26156 q = 1) (hb : d152855 q = 1) : d248905 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26156, d248905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26156, d248905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26165 q = 1) (hb : d152855 q = 1) : d248914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26165, d248914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62294 q ha hb
    | true =>
      simp only [d26165, d248914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62297 q ha hb
  have h4 (q : Pattern) (ha : d26166 q = 1) (hb : d152855 q = 1) : d248915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26166, d248915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26166, d248915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26167 q = 1) (hb : d152855 q = 1) : d248916 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d26167, d248916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26167, d248916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202141 q = 1) : d248996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202141, d248996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62320 q ha hb
    | true =>
      simp only [d202141, d248996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62327 q ha hb
  have h7 (q : Pattern) (ha : d26359 q = 1) (hb : d152855 q = 1) : d249009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26359, d249009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62298 q ha hb
    | true =>
      simp only [d26359, d249009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62299 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202142 q = 1) : d249010 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202142, d249010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202142, d249010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202143 q = 1) : d249011 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202143, d249011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202143, d249011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d202144 q = 1) : d249012 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202144, d249012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d202144, d249012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d202148 q = 1) : d249016 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202148, d249016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202148, d249016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62328 q ha hb
  have h12 (q : Pattern) (ha : d26368 q = 1) (hb : d152855 q = 1) : d249018 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26368, d249018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26368, d249018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62300 q ha hb
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202149 q = 1) : d249019 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202149, d249019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202149, d249019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202150 q = 1) : d249020 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202150, d249020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202150, d249020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202151 q = 1) : d249021 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202151, d249021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202151, d249021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d152855 q = 1) (hb : d202152 q = 1) : d249022 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202152, d249022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202152, d249022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d152855 q = 1) (hb : d202158 q = 1) : d249098 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202158, d249098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202158, d249098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62339 q ha hb
  have h18 (q : Pattern) (ha : d26535 q = 1) (hb : d152855 q = 1) : d249109 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26535, d249109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26535, d249109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62305 q ha hb
  have h19 (q : Pattern) (ha : d152855 q = 1) (hb : d202159 q = 1) : d249110 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202159, d249110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202159, d249110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d152855 q = 1) (hb : d202160 q = 1) : d249111 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202160, d249111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202160, d249111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d152855 q = 1) (hb : d202161 q = 1) : d249112 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202161, d249112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202161, d249112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d152855 q = 1) (hb : d202162 q = 1) : d249113 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202162, d249113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202162, d249113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202163 q = 1) : d249114 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202163, d249114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202163, d249114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62341 (p : Pattern) (ha : d152855 p = 1) (hb : d202169 p = 1) : d249120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202164 q = 1) : d249115 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202164, d249115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202164, d249115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62340 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202165 q = 1) : d249116 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202165, d249116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202165, d249116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202166 q = 1) : d249117 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202166, d249117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202166, d249117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202167 q = 1) : d249118 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202167, d249118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202167, d249118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202168 q = 1) : d249119 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202168, d249119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202168, d249119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202169 q = 1) : d249120 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202169, d249120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202169, d249120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62342 (p : Pattern) (ha : d26550 p = 1) (hb : d152854 p = 1) : d249124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26187 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10053 q = 1) (hb : d152852 q = 1) : d10053 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26550 q = 1) (hb : d152854 q = 1) : d249124 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26550, d152854, d249124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26550, d152854, d249124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62343 (p : Pattern) (ha : d26561 p = 1) (hb : d152854 p = 1) : d249129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26557 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26560 q = 1) (hb : d152852 q = 1) : d26560 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26561 q = 1) (hb : d152854 q = 1) : d249129 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26561, d152854, d249129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26561, d152854, d249129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62344 (p : Pattern) (ha : d26580 p = 1) (hb : d152855 p = 1) : d249135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26551 q = 1) (hb : d152854 q = 1) : d249125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26551, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62342 q ha hb
    | true =>
      simp only [d26551, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26552 q = 1) (hb : d152854 q = 1) : d249126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26552, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26552, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26553 q = 1) (hb : d152854 q = 1) : d249127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26553, d249127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26553, d249127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26554 q = 1) (hb : d152854 q = 1) : d249128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26554, d249128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26554, d249128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26562 q = 1) (hb : d152854 q = 1) : d249130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26562, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62343 q ha hb
    | true =>
      simp only [d26562, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26563 q = 1) (hb : d152854 q = 1) : d249131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26563, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26563, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26564 q = 1) (hb : d152854 q = 1) : d249132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26564, d249132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26564, d249132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26565 q = 1) (hb : d152854 q = 1) : d249133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26565, d249133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26565, d249133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26566 q = 1) (hb : d152854 q = 1) : d249134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26566, d249134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26566, d249134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26579 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26580 q = 1) (hb : d152855 q = 1) : d249135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26580, d152855, d249135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26580, d152855, d249135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62345 (p : Pattern) (ha : d26574 p = 1) (hb : d152854 p = 1) : d249141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10133 q = 1) (hb : d152852 q = 1) : d10133 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26574 q = 1) (hb : d152854 q = 1) : d249141 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26574, d152854, d249141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26574, d152854, d249141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62346 (p : Pattern) (ha : d26583 p = 1) (hb : d152854 p = 1) : d249136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26557 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26582 q = 1) (hb : d152852 q = 1) : d26582 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26583 q = 1) (hb : d152854 q = 1) : d249136 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26583, d152854, d249136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26583, d152854, d249136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62347 (p : Pattern) (ha : d26590 p = 1) (hb : d152855 p = 1) : d249147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26584 q = 1) (hb : d152854 q = 1) : d249137 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26584, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62346 q ha hb
    | true =>
      simp only [d26584, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26585 q = 1) (hb : d152854 q = 1) : d249138 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26585, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26585, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26586 q = 1) (hb : d152854 q = 1) : d249139 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26586, d249139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26586, d249139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26587 q = 1) (hb : d152854 q = 1) : d249140 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26587, d249140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26587, d249140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26575 q = 1) (hb : d152854 q = 1) : d249142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
    | true =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26576 q = 1) (hb : d152854 q = 1) : d249143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26577 q = 1) (hb : d152854 q = 1) : d249144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26577, d249144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26577, d249144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26578 q = 1) (hb : d152854 q = 1) : d249145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26578, d249145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26578, d249145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26588 q = 1) (hb : d152854 q = 1) : d249146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26588, d249146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26588, d249146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26589 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26590 q = 1) (hb : d152855 q = 1) : d249147 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26590, d152855, d249147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26590, d152855, d249147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62348 (p : Pattern) (ha : d26594 p = 1) (hb : d152855 p = 1) : d249152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26575 q = 1) (hb : d152854 q = 1) : d249142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
    | true =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26576 q = 1) (hb : d152854 q = 1) : d249143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26577 q = 1) (hb : d152854 q = 1) : d249144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26577, d249144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26577, d249144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26578 q = 1) (hb : d152854 q = 1) : d249145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26578, d249145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26578, d249145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26589 q = 1) (hb : d152854 q = 1) : d249151 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26589, d249151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26589, d249151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15165 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d26594 q = 1) (hb : d152855 q = 1) : d249152 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26594, d152855, d249152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26594, d152855, d249152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62349 (p : Pattern) (ha : d26601 p = 1) (hb : d152855 p = 1) : d249159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26591 q = 1) (hb : d152855 q = 1) : d249148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26591, d249148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62344 q ha hb
    | true =>
      simp only [d26591, d249148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62347 q ha hb
  have h2 (q : Pattern) (ha : d26592 q = 1) (hb : d152855 q = 1) : d249149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26592, d249149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26592, d249149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26593 q = 1) (hb : d152855 q = 1) : d249150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26593, d249150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26593, d249150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26595 q = 1) (hb : d152855 q = 1) : d249153 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26595, d249153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62347 q ha hb
    | true =>
      simp only [d26595, d249153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62348 q ha hb
  have h5 (q : Pattern) (ha : d26596 q = 1) (hb : d152855 q = 1) : d249154 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26596, d249154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26596, d249154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26597 q = 1) (hb : d152855 q = 1) : d249155 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26597, d249155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26597, d249155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26598 q = 1) (hb : d152855 q = 1) : d249156 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26598, d249156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26598, d249156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26599 q = 1) (hb : d152855 q = 1) : d249157 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26599, d249157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26599, d249157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26600 q = 1) (hb : d152855 q = 1) : d249158 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26600, d249158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26600, d249158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26601 q = 1) (hb : d152855 q = 1) : d249159 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26601, d249159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26601, d249159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62350 (p : Pattern) (ha : d26605 p = 1) (hb : d152855 p = 1) : d249163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26595 q = 1) (hb : d152855 q = 1) : d249153 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26595, d249153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62347 q ha hb
    | true =>
      simp only [d26595, d249153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62348 q ha hb
  have h2 (q : Pattern) (ha : d26596 q = 1) (hb : d152855 q = 1) : d249154 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26596, d249154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26596, d249154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26597 q = 1) (hb : d152855 q = 1) : d249155 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26597, d249155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26597, d249155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26599 q = 1) (hb : d152855 q = 1) : d249157 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26599, d249157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26599, d249157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26604 q = 1) (hb : d152855 q = 1) : d249162 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26604, d249162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26604, d249162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26605 q = 1) (hb : d152855 q = 1) : d249163 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26605, d249163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26605, d249163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62351 (p : Pattern) (ha : d26611 p = 1) (hb : d152855 p = 1) : d249169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d152855 q = 1) : d249160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62349 q ha hb
    | true =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d152855 q = 1) : d249161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d152855 q = 1) : d249166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26609 q = 1) (hb : d152855 q = 1) : d249167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26609, d249167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26609, d249167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26610 q = 1) (hb : d152855 q = 1) : d249168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26610, d249168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26610, d249168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26611 q = 1) (hb : d152855 q = 1) : d249169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26611, d249169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26611, d249169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62352 (p : Pattern) (ha : d26615 p = 1) (hb : d152855 p = 1) : d249173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d152855 q = 1) : d249170 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26613 q = 1) (hb : d152855 q = 1) : d249171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26613, d249171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26613, d249171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26614 q = 1) (hb : d152855 q = 1) : d249172 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26614, d249172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26614, d249172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26615 q = 1) (hb : d152855 q = 1) : d249173 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26615, d249173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26615, d249173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62353 (p : Pattern) (ha : d26621 p = 1) (hb : d152855 p = 1) : d249179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26616 q = 1) (hb : d152855 q = 1) : d249174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26616, d249174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62351 q ha hb
    | true =>
      simp only [d26616, d249174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62352 q ha hb
  have h2 (q : Pattern) (ha : d26617 q = 1) (hb : d152855 q = 1) : d249175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26617, d249175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26617, d249175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26618 q = 1) (hb : d152855 q = 1) : d249176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26618, d249176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26618, d249176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26619 q = 1) (hb : d152855 q = 1) : d249177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26619, d249177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26619, d249177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26620 q = 1) (hb : d152855 q = 1) : d249178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26620, d249178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26620, d249178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26621 q = 1) (hb : d152855 q = 1) : d249179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26621, d249179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26621, d249179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62354 (p : Pattern) (ha : d26624 p = 1) (hb : d152855 p = 1) : d249182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d152855 q = 1) : d249160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62349 q ha hb
    | true =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d152855 q = 1) : d249161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d152855 q = 1) : d249166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26609 q = 1) (hb : d152855 q = 1) : d249167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26609, d249167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26609, d249167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26610 q = 1) (hb : d152855 q = 1) : d249168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26610, d249168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26610, d249168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26624 q = 1) (hb : d152855 q = 1) : d249182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26624, d249182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26624, d249182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62355 (p : Pattern) (ha : d26625 p = 1) (hb : d152855 p = 1) : d249183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d152855 q = 1) : d249170 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26613 q = 1) (hb : d152855 q = 1) : d249171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26613, d249171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26613, d249171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26614 q = 1) (hb : d152855 q = 1) : d249172 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26614, d249172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26614, d249172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26625 q = 1) (hb : d152855 q = 1) : d249183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26625, d249183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26625, d249183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62356 (p : Pattern) (ha : d26631 p = 1) (hb : d152855 p = 1) : d249189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26616 q = 1) (hb : d152855 q = 1) : d249174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26616, d249174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62351 q ha hb
    | true =>
      simp only [d26616, d249174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62352 q ha hb
  have h2 (q : Pattern) (ha : d26617 q = 1) (hb : d152855 q = 1) : d249175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26617, d249175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26617, d249175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26618 q = 1) (hb : d152855 q = 1) : d249176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26618, d249176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26618, d249176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26619 q = 1) (hb : d152855 q = 1) : d249177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26619, d249177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26619, d249177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26620 q = 1) (hb : d152855 q = 1) : d249178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26620, d249178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26620, d249178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26626 q = 1) (hb : d152855 q = 1) : d249184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26626, d249184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62354 q ha hb
    | true =>
      simp only [d26626, d249184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62355 q ha hb
  have h7 (q : Pattern) (ha : d26627 q = 1) (hb : d152855 q = 1) : d249185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26627, d249185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26627, d249185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26628 q = 1) (hb : d152855 q = 1) : d249186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26628, d249186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26628, d249186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26629 q = 1) (hb : d152855 q = 1) : d249187 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26629, d249187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26629, d249187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26630 q = 1) (hb : d152855 q = 1) : d249188 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26630, d249188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26630, d249188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26631 q = 1) (hb : d152855 q = 1) : d249189 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26631, d249189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26631, d249189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62357 (p : Pattern) (ha : d26813 p = 1) (hb : d152855 p = 1) : d249276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26616 q = 1) (hb : d152855 q = 1) : d249174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26616, d249174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62351 q ha hb
    | true =>
      simp only [d26616, d249174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62352 q ha hb
  have h2 (q : Pattern) (ha : d26617 q = 1) (hb : d152855 q = 1) : d249175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26617, d249175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26617, d249175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26618 q = 1) (hb : d152855 q = 1) : d249176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26618, d249176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26618, d249176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26619 q = 1) (hb : d152855 q = 1) : d249177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26619, d249177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26619, d249177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26620 q = 1) (hb : d152855 q = 1) : d249178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26620, d249178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26620, d249178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26808 q = 1) (hb : d152855 q = 1) : d249271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26808, d249271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62352 q ha hb
    | true =>
      simp only [d26808, d249271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26809 q = 1) (hb : d152855 q = 1) : d249272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26809, d249272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26809, d249272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26810 q = 1) (hb : d152855 q = 1) : d249273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26810, d249273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26810, d249273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26811 q = 1) (hb : d152855 q = 1) : d249274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26811, d249274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26811, d249274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26812 q = 1) (hb : d152855 q = 1) : d249275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26812, d249275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26812, d249275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26813 q = 1) (hb : d152855 q = 1) : d249276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26813, d249276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26813, d249276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62358 (p : Pattern) (ha : d26819 p = 1) (hb : d152855 p = 1) : d249282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26808 q = 1) (hb : d152855 q = 1) : d249271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26808, d249271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62352 q ha hb
    | true =>
      simp only [d26808, d249271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26809 q = 1) (hb : d152855 q = 1) : d249272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26809, d249272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26809, d249272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26810 q = 1) (hb : d152855 q = 1) : d249273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26810, d249273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26810, d249273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26811 q = 1) (hb : d152855 q = 1) : d249274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26811, d249274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26811, d249274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26812 q = 1) (hb : d152855 q = 1) : d249275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26812, d249275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26812, d249275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26814 q = 1) (hb : d152855 q = 1) : d249277 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26814, d249277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62355 q ha hb
    | true =>
      simp only [d26814, d249277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26815 q = 1) (hb : d152855 q = 1) : d249278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26815, d249278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26815, d249278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26816 q = 1) (hb : d152855 q = 1) : d249279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26816, d249279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26816, d249279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26817 q = 1) (hb : d152855 q = 1) : d249280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26817, d249280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26817, d249280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26818 q = 1) (hb : d152855 q = 1) : d249281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26818, d249281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26818, d249281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26819 q = 1) (hb : d152855 q = 1) : d249282 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26819, d249282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26819, d249282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62359 (p : Pattern) (ha : d26828 p = 1) (hb : d152855 p = 1) : d249291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26814 q = 1) (hb : d152855 q = 1) : d249277 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26814, d249277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62355 q ha hb
    | true =>
      simp only [d26814, d249277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26815 q = 1) (hb : d152855 q = 1) : d249278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26815, d249278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26815, d249278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26816 q = 1) (hb : d152855 q = 1) : d249279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26816, d249279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26816, d249279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26817 q = 1) (hb : d152855 q = 1) : d249280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26817, d249280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26817, d249280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26818 q = 1) (hb : d152855 q = 1) : d249281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26818, d249281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26818, d249281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26828 q = 1) (hb : d152855 q = 1) : d249291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26828, d249291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26828, d249291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62360 (p : Pattern) (ha : d26878 p = 1) (hb : d152855 p = 1) : d249327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26873 q = 1) (hb : d152854 q = 1) : d249322 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26873, d249322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26873, d249322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62346 q ha hb
  have h2 (q : Pattern) (ha : d26584 q = 1) (hb : d152854 q = 1) : d249137 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26584, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62346 q ha hb
    | true =>
      simp only [d26584, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26874 q = 1) (hb : d152854 q = 1) : d249323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26874, d249323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26874, d249323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26585 q = 1) (hb : d152854 q = 1) : d249138 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26585, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26585, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26875 q = 1) (hb : d152854 q = 1) : d249324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26875, d249324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26875, d249324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26876 q = 1) (hb : d152854 q = 1) : d249325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26876, d249325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26876, d249325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26858 q = 1) (hb : d152854 q = 1) : d249312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26858, d249312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26858, d249312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
  have h8 (q : Pattern) (ha : d26575 q = 1) (hb : d152854 q = 1) : d249142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
    | true =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26859 q = 1) (hb : d152854 q = 1) : d249313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26859, d249313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26859, d249313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26576 q = 1) (hb : d152854 q = 1) : d249143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26860 q = 1) (hb : d152854 q = 1) : d249314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26860, d249314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26860, d249314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26861 q = 1) (hb : d152854 q = 1) : d249315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26861, d249315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26861, d249315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26877 q = 1) (hb : d152854 q = 1) : d249326 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26877, d249326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26877, d249326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26867 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26878 q = 1) (hb : d152855 q = 1) : d249327 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26878, d152855, d249327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26878, d152855, d249327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62361 (p : Pattern) (ha : d26882 p = 1) (hb : d152855 p = 1) : d249332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26858 q = 1) (hb : d152854 q = 1) : d249312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26858, d249312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26858, d249312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
  have h2 (q : Pattern) (ha : d26575 q = 1) (hb : d152854 q = 1) : d249142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
    | true =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26859 q = 1) (hb : d152854 q = 1) : d249313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26859, d249313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26859, d249313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26576 q = 1) (hb : d152854 q = 1) : d249143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26860 q = 1) (hb : d152854 q = 1) : d249314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26860, d249314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26860, d249314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26861 q = 1) (hb : d152854 q = 1) : d249315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26861, d249315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26861, d249315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26867 q = 1) (hb : d152854 q = 1) : d249331 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26867, d249331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26867, d249331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15416 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d26882 q = 1) (hb : d152855 q = 1) : d249332 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26882, d152855, d249332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26882, d152855, d249332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62362 (p : Pattern) (ha : d26901 p = 1) (hb : d152855 p = 1) : d249351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26883 q = 1) (hb : d152855 q = 1) : d249333 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26883, d249333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62360 q ha hb
    | true =>
      simp only [d26883, d249333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62361 q ha hb
  have h2 (q : Pattern) (ha : d26884 q = 1) (hb : d152855 q = 1) : d249334 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26884, d249334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26884, d249334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26885 q = 1) (hb : d152855 q = 1) : d249335 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26885, d249335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26885, d249335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26891 q = 1) (hb : d152855 q = 1) : d249341 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26891, d249341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26891, d249341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26900 q = 1) (hb : d152855 q = 1) : d249350 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26900, d249350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26900, d249350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26901 q = 1) (hb : d152855 q = 1) : d249351 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26901, d249351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26901, d249351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62363 (p : Pattern) (ha : d26991 p = 1) (hb : d152855 p = 1) : d249382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26902 q = 1) (hb : d152855 q = 1) : d249352 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26902, d249352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62362 q ha hb
    | true =>
      simp only [d26902, d249352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26903 q = 1) (hb : d152855 q = 1) : d249353 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26903, d249353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26903, d249353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26988 q = 1) (hb : d152855 q = 1) : d249379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26988, d249379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26988, d249379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26989 q = 1) (hb : d152855 q = 1) : d249380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26989, d249380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26989, d249380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26990 q = 1) (hb : d152855 q = 1) : d249381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26990, d249381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26990, d249381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26991 q = 1) (hb : d152855 q = 1) : d249382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26991, d249382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26991, d249382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62364 (p : Pattern) (ha : d26997 p = 1) (hb : d152855 p = 1) : d249388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26992 q = 1) (hb : d152855 q = 1) : d249383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26992, d249383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62363 q ha hb
    | true =>
      simp only [d26992, d249383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26993 q = 1) (hb : d152855 q = 1) : d249384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26993, d249384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26993, d249384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26994 q = 1) (hb : d152855 q = 1) : d249385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26994, d249385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26994, d249385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26995 q = 1) (hb : d152855 q = 1) : d249386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26995, d249386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26995, d249386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26996 q = 1) (hb : d152855 q = 1) : d249387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26996, d249387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26996, d249387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26997 q = 1) (hb : d152855 q = 1) : d249388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26997, d249388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26997, d249388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62365 (p : Pattern) (ha : d26636 p = 1) (hb : d152855 p = 1) : d249194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d152855 q = 1) : d249160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62349 q ha hb
    | true =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d152855 q = 1) : d249161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d152855 q = 1) : d249166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26609 q = 1) (hb : d152855 q = 1) : d249167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26609, d249167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26609, d249167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26635 q = 1) (hb : d152855 q = 1) : d249193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26635, d249193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26635, d249193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26636 q = 1) (hb : d152855 q = 1) : d249194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26636, d249194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26636, d249194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62366 (p : Pattern) (ha : d26638 p = 1) (hb : d152855 p = 1) : d249196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d152855 q = 1) : d249170 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26613 q = 1) (hb : d152855 q = 1) : d249171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26613, d249171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26613, d249171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26637 q = 1) (hb : d152855 q = 1) : d249195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26637, d249195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26637, d249195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26638 q = 1) (hb : d152855 q = 1) : d249196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26638, d249196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26638, d249196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62367 (p : Pattern) (ha : d26645 p = 1) (hb : d152855 p = 1) : d249203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d152855 q = 1) : d249160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62349 q ha hb
    | true =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d152855 q = 1) : d249161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d152855 q = 1) : d249166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26643 q = 1) (hb : d152855 q = 1) : d249201 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26643, d249201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26643, d249201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26644 q = 1) (hb : d152855 q = 1) : d249202 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26644, d249202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26644, d249202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26645 q = 1) (hb : d152855 q = 1) : d249203 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26645, d249203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26645, d249203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62368 (p : Pattern) (ha : d26648 p = 1) (hb : d152855 p = 1) : d249206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d152855 q = 1) : d249170 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26646 q = 1) (hb : d152855 q = 1) : d249204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26646, d249204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26646, d249204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26647 q = 1) (hb : d152855 q = 1) : d249205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26647, d249205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26647, d249205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26648 q = 1) (hb : d152855 q = 1) : d249206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26648, d249206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26648, d249206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62369 (p : Pattern) (ha : d26664 p = 1) (hb : d152855 p = 1) : d249211 p = 1 := by
  have h0 (q : Pattern) (ha : d26656 q = 1) (hb : d152854 q = 1) : d26656 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26551 q = 1) (hb : d152854 q = 1) : d249125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26551, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62342 q ha hb
    | true =>
      simp only [d26551, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26552 q = 1) (hb : d152854 q = 1) : d249126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26552, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26552, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d26553 q = 1) (hb : d152854 q = 1) : d249127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26553, d249127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26553, d249127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26554 q = 1) (hb : d152854 q = 1) : d249128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26554, d249128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26554, d249128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d26657 q = 1) (hb : d152854 q = 1) : d249210 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26657, d249210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26657, d249210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d26663 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d26664 q = 1) (hb : d152855 q = 1) : d249211 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26664, d152855, d249211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26664, d152855, d249211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62370 (p : Pattern) (ha : d26567 p = 1) (hb : d152854 p = 1) : d249129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10053 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26560 q = 1) (hb : d152852 q = 1) : d26560 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26567 q = 1) (hb : d152854 q = 1) : d249129 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26567, d152854, d249129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26567, d152854, d249129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62371 (p : Pattern) (ha : d26668 p = 1) (hb : d152855 p = 1) : d249216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26568 q = 1) (hb : d152854 q = 1) : d249130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62370 q ha hb
    | true =>
      simp only [d26568, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26569 q = 1) (hb : d152854 q = 1) : d249131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26569, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26570 q = 1) (hb : d152854 q = 1) : d249132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26570, d249132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26570, d249132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26571 q = 1) (hb : d152854 q = 1) : d249133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26571, d249133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26571, d249133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26575 q = 1) (hb : d152854 q = 1) : d249142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
    | true =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26576 q = 1) (hb : d152854 q = 1) : d249143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26577 q = 1) (hb : d152854 q = 1) : d249144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26577, d249144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26577, d249144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26578 q = 1) (hb : d152854 q = 1) : d249145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26578, d249145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26578, d249145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26579 q = 1) (hb : d152854 q = 1) : d249215 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26579, d249215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26579, d249215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26589 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26668 q = 1) (hb : d152855 q = 1) : d249216 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26668, d152855, d249216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26668, d152855, d249216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62372 (p : Pattern) (ha : d26674 p = 1) (hb : d152855 p = 1) : d249222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26665 q = 1) (hb : d152855 q = 1) : d249212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26665, d249212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62369 q ha hb
    | true =>
      simp only [d26665, d249212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62344 q ha hb
  have h2 (q : Pattern) (ha : d26666 q = 1) (hb : d152855 q = 1) : d249213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26666, d249213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26666, d249213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26667 q = 1) (hb : d152855 q = 1) : d249214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26667, d249214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26667, d249214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26669 q = 1) (hb : d152855 q = 1) : d249217 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26669, d249217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62344 q ha hb
    | true =>
      simp only [d26669, d249217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62371 q ha hb
  have h5 (q : Pattern) (ha : d26670 q = 1) (hb : d152855 q = 1) : d249218 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26670, d249218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26670, d249218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26671 q = 1) (hb : d152855 q = 1) : d249219 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26671, d249219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26671, d249219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26672 q = 1) (hb : d152855 q = 1) : d249220 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26672, d249220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26672, d249220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26591 q = 1) (hb : d152855 q = 1) : d249148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26591, d249148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62344 q ha hb
    | true =>
      simp only [d26591, d249148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62347 q ha hb
  have h9 (q : Pattern) (ha : d26592 q = 1) (hb : d152855 q = 1) : d249149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26592, d249149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26592, d249149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26593 q = 1) (hb : d152855 q = 1) : d249150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26593, d249150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26593, d249150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26595 q = 1) (hb : d152855 q = 1) : d249153 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26595, d249153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62347 q ha hb
    | true =>
      simp only [d26595, d249153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62348 q ha hb
  have h12 (q : Pattern) (ha : d26596 q = 1) (hb : d152855 q = 1) : d249154 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26596, d249154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26596, d249154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26597 q = 1) (hb : d152855 q = 1) : d249155 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26597, d249155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26597, d249155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26598 q = 1) (hb : d152855 q = 1) : d249156 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26598, d249156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26598, d249156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26673 q = 1) (hb : d152855 q = 1) : d249221 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26673, d249221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26673, d249221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d26674 q = 1) (hb : d152855 q = 1) : d249222 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26674, d249222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26674, d249222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62373 (p : Pattern) (ha : d26680 p = 1) (hb : d152855 p = 1) : d249228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26675 q = 1) (hb : d152855 q = 1) : d249223 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26675, d249223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62372 q ha hb
    | true =>
      simp only [d26675, d249223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26676 q = 1) (hb : d152855 q = 1) : d249224 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26676, d249224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26676, d249224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26602 q = 1) (hb : d152855 q = 1) : d249160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62349 q ha hb
    | true =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26603 q = 1) (hb : d152855 q = 1) : d249161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26677 q = 1) (hb : d152855 q = 1) : d249225 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26677, d249225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26677, d249225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26678 q = 1) (hb : d152855 q = 1) : d249226 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26678, d249226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26678, d249226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26679 q = 1) (hb : d152855 q = 1) : d249227 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26679, d249227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26679, d249227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26680 q = 1) (hb : d152855 q = 1) : d249228 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26680, d249228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26680, d249228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62374 (p : Pattern) (ha : d26763 p = 1) (hb : d152855 p = 1) : d249147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26584 q = 1) (hb : d152854 q = 1) : d249137 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26584, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62346 q ha hb
    | true =>
      simp only [d26584, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26585 q = 1) (hb : d152854 q = 1) : d249138 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26585, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26585, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26586 q = 1) (hb : d152854 q = 1) : d249139 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26586, d249139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26586, d249139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26587 q = 1) (hb : d152854 q = 1) : d249140 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26587, d249140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26587, d249140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26575 q = 1) (hb : d152854 q = 1) : d249142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
    | true =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26576 q = 1) (hb : d152854 q = 1) : d249143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26577 q = 1) (hb : d152854 q = 1) : d249144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26577, d249144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26577, d249144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26578 q = 1) (hb : d152854 q = 1) : d249145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26578, d249145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26578, d249145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26588 q = 1) (hb : d152854 q = 1) : d249146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26588, d249146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26588, d249146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26762 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26763 q = 1) (hb : d152855 q = 1) : d249147 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26763, d152855, d249147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26763, d152855, d249147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62375 (p : Pattern) (ha : d26757 p = 1) (hb : d152854 p = 1) : d157412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26756 q = 1) (hb : d152852 q = 1) : d26756 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26757 q = 1) (hb : d152854 q = 1) : d157412 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26757, d152854, d157412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d26757, d152854, d157412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62376 (p : Pattern) (ha : d26764 p = 1) (hb : d152855 p = 1) : d157418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26758 q = 1) (hb : d152854 q = 1) : d157413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26758, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62375 q ha hb
    | true =>
      simp only [d26758, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26759 q = 1) (hb : d152854 q = 1) : d157414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26759, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26759, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26760 q = 1) (hb : d152854 q = 1) : d157415 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26760, d157415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26760, d157415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26761 q = 1) (hb : d152854 q = 1) : d157416 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26761, d157416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26761, d157416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26762 q = 1) (hb : d152854 q = 1) : d157417 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26762, d157417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26762, d157417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d26764 q = 1) (hb : d152855 q = 1) : d157418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26764, d152855, d157418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26764, d152855, d157418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62377 (p : Pattern) (ha : d26770 p = 1) (hb : d152855 p = 1) : d249236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26591 q = 1) (hb : d152855 q = 1) : d249148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26591, d249148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62344 q ha hb
    | true =>
      simp only [d26591, d249148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62347 q ha hb
  have h2 (q : Pattern) (ha : d26592 q = 1) (hb : d152855 q = 1) : d249149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26592, d249149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26592, d249149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26593 q = 1) (hb : d152855 q = 1) : d249150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26593, d249150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26593, d249150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26595 q = 1) (hb : d152855 q = 1) : d249153 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26595, d249153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62347 q ha hb
    | true =>
      simp only [d26595, d249153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62348 q ha hb
  have h5 (q : Pattern) (ha : d26596 q = 1) (hb : d152855 q = 1) : d249154 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26596, d249154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26596, d249154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26597 q = 1) (hb : d152855 q = 1) : d249155 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26597, d249155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26597, d249155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26598 q = 1) (hb : d152855 q = 1) : d249156 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26598, d249156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26598, d249156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26765 q = 1) (hb : d152855 q = 1) : d249231 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26765, d249231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62374 q ha hb
    | true =>
      simp only [d26765, d249231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62376 q ha hb
  have h9 (q : Pattern) (ha : d26766 q = 1) (hb : d152855 q = 1) : d249232 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26766, d249232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26766, d249232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26767 q = 1) (hb : d152855 q = 1) : d249233 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26767, d249233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26767, d249233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26768 q = 1) (hb : d152855 q = 1) : d249234 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26768, d249234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26768, d249234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26769 q = 1) (hb : d152855 q = 1) : d249235 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26769, d249235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26769, d249235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26770 q = 1) (hb : d152855 q = 1) : d249236 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26770, d249236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26770, d249236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro62378 (p : Pattern) (ha : d26776 p = 1) (hb : d152855 p = 1) : d249242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26771 q = 1) (hb : d152855 q = 1) : d249237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26771, d249237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62377 q ha hb
    | true =>
      simp only [d26771, d249237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26772 q = 1) (hb : d152855 q = 1) : d249238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26772, d249238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26772, d249238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26773 q = 1) (hb : d152855 q = 1) : d249239 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26773, d249239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26773, d249239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26774 q = 1) (hb : d152855 q = 1) : d249240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26774, d249240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26774, d249240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26775 q = 1) (hb : d152855 q = 1) : d249241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26775, d249241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26775, d249241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26776 q = 1) (hb : d152855 q = 1) : d249242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26776, d249242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26776, d249242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62379 (p : Pattern) (ha : d152855 p = 1) (hb : d202177 p = 1) : d249248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26639 q = 1) (hb : d152855 q = 1) : d249197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26639, d249197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62365 q ha hb
    | true =>
      simp only [d26639, d249197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62366 q ha hb
  have h2 (q : Pattern) (ha : d26640 q = 1) (hb : d152855 q = 1) : d249198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26640, d249198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26640, d249198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26641 q = 1) (hb : d152855 q = 1) : d249199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26641, d249199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26641, d249199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26642 q = 1) (hb : d152855 q = 1) : d249200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26642, d249200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26642, d249200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26649 q = 1) (hb : d152855 q = 1) : d249207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26649, d249207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62367 q ha hb
    | true =>
      simp only [d26649, d249207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62368 q ha hb
  have h6 (q : Pattern) (ha : d26650 q = 1) (hb : d152855 q = 1) : d249208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26650, d249208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26650, d249208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26651 q = 1) (hb : d152855 q = 1) : d249209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26651, d249209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26651, d249209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26681 q = 1) (hb : d152855 q = 1) : d249229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26681, d249229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62373 q ha hb
    | true =>
      simp only [d26681, d249229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62351 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202173 q = 1) : d249230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202173, d249230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202173, d249230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d26777 q = 1) (hb : d152855 q = 1) : d249243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26777, d249243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62378 q ha hb
    | true =>
      simp only [d26777, d249243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26778 q = 1) (hb : d152855 q = 1) : d249244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26778, d249244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26778, d249244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202174 q = 1) : d249245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202174, d249245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202174, d249245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202175 q = 1) : d249246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202175, d249246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202175, d249246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202176 q = 1) : d249247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202176, d249247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202176, d249247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202177 q = 1) : d249248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202177, d249248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202177, d249248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62380 (p : Pattern) (ha : d26783 p = 1) (hb : d152855 p = 1) : d249249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d152855 q = 1) : d249160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62349 q ha hb
    | true =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d152855 q = 1) : d249161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d152855 q = 1) : d249166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26609 q = 1) (hb : d152855 q = 1) : d249167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26609, d249167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26609, d249167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26635 q = 1) (hb : d152855 q = 1) : d249193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26635, d249193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26635, d249193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26783 q = 1) (hb : d152855 q = 1) : d249249 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26783, d249249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26783, d249249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62381 (p : Pattern) (ha : d26784 p = 1) (hb : d152855 p = 1) : d249250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d152855 q = 1) : d249170 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26613 q = 1) (hb : d152855 q = 1) : d249171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26613, d249171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26613, d249171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26637 q = 1) (hb : d152855 q = 1) : d249195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26637, d249195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26637, d249195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26784 q = 1) (hb : d152855 q = 1) : d249250 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26784, d249250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26784, d249250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62382 (p : Pattern) (ha : d26789 p = 1) (hb : d152855 p = 1) : d249255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d152855 q = 1) : d249160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62349 q ha hb
    | true =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d152855 q = 1) : d249161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d152855 q = 1) : d249166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d249166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26643 q = 1) (hb : d152855 q = 1) : d249201 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26643, d249201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26643, d249201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26644 q = 1) (hb : d152855 q = 1) : d249202 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26644, d249202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26644, d249202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26789 q = 1) (hb : d152855 q = 1) : d249255 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26789, d249255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26789, d249255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62383 (p : Pattern) (ha : d26790 p = 1) (hb : d152855 p = 1) : d249256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d152855 q = 1) : d249164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62350 q ha hb
    | true =>
      simp only [d26606, d249164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d152855 q = 1) : d249165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d249165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d152855 q = 1) : d249170 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d249170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26646 q = 1) (hb : d152855 q = 1) : d249204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26646, d249204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26646, d249204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26647 q = 1) (hb : d152855 q = 1) : d249205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26647, d249205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26647, d249205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26790 q = 1) (hb : d152855 q = 1) : d249256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26790, d249256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26790, d249256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62384 (p : Pattern) (ha : d26794 p = 1) (hb : d152855 p = 1) : d249260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26675 q = 1) (hb : d152855 q = 1) : d249223 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26675, d249223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62372 q ha hb
    | true =>
      simp only [d26675, d249223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26676 q = 1) (hb : d152855 q = 1) : d249224 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26676, d249224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26676, d249224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26602 q = 1) (hb : d152855 q = 1) : d249160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62349 q ha hb
    | true =>
      simp only [d26602, d249160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26603 q = 1) (hb : d152855 q = 1) : d249161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d249161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26677 q = 1) (hb : d152855 q = 1) : d249225 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26677, d249225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26677, d249225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26678 q = 1) (hb : d152855 q = 1) : d249226 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26678, d249226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26678, d249226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26679 q = 1) (hb : d152855 q = 1) : d249227 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26679, d249227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26679, d249227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26794 q = 1) (hb : d152855 q = 1) : d249260 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26794, d249260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26794, d249260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62385 (p : Pattern) (ha : d26800 p = 1) (hb : d152855 p = 1) : d249263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26771 q = 1) (hb : d152855 q = 1) : d249237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26771, d249237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62377 q ha hb
    | true =>
      simp only [d26771, d249237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26772 q = 1) (hb : d152855 q = 1) : d249238 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26772, d249238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26772, d249238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26773 q = 1) (hb : d152855 q = 1) : d249239 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26773, d249239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26773, d249239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26774 q = 1) (hb : d152855 q = 1) : d249240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26774, d249240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26774, d249240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26775 q = 1) (hb : d152855 q = 1) : d249241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26775, d249241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26775, d249241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26800 q = 1) (hb : d152855 q = 1) : d249263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26800, d249263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26800, d249263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62386 (p : Pattern) (ha : d152855 p = 1) (hb : d202182 p = 1) : d249269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26639 q = 1) (hb : d152855 q = 1) : d249197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26639, d249197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62365 q ha hb
    | true =>
      simp only [d26639, d249197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62366 q ha hb
  have h2 (q : Pattern) (ha : d26640 q = 1) (hb : d152855 q = 1) : d249198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26640, d249198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26640, d249198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26641 q = 1) (hb : d152855 q = 1) : d249199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26641, d249199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26641, d249199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26642 q = 1) (hb : d152855 q = 1) : d249200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26642, d249200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26642, d249200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26649 q = 1) (hb : d152855 q = 1) : d249207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26649, d249207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62367 q ha hb
    | true =>
      simp only [d26649, d249207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62368 q ha hb
  have h6 (q : Pattern) (ha : d26650 q = 1) (hb : d152855 q = 1) : d249208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26650, d249208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26650, d249208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26651 q = 1) (hb : d152855 q = 1) : d249209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26651, d249209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26651, d249209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26681 q = 1) (hb : d152855 q = 1) : d249229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26681, d249229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62373 q ha hb
    | true =>
      simp only [d26681, d249229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62351 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202173 q = 1) : d249230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202173, d249230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202173, d249230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d26777 q = 1) (hb : d152855 q = 1) : d249243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26777, d249243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62378 q ha hb
    | true =>
      simp only [d26777, d249243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26778 q = 1) (hb : d152855 q = 1) : d249244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26778, d249244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26778, d249244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202174 q = 1) : d249245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202174, d249245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202174, d249245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202175 q = 1) : d249246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202175, d249246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202175, d249246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202176 q = 1) : d249247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202176, d249247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202176, d249247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26785 q = 1) (hb : d152855 q = 1) : d249251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26785, d249251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62380 q ha hb
    | true =>
      simp only [d26785, d249251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62381 q ha hb
  have h16 (q : Pattern) (ha : d26786 q = 1) (hb : d152855 q = 1) : d249252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26786, d249252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26786, d249252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d26787 q = 1) (hb : d152855 q = 1) : d249253 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26787, d249253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d26787, d249253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d26788 q = 1) (hb : d152855 q = 1) : d249254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26788, d249254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26788, d249254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d26791 q = 1) (hb : d152855 q = 1) : d249257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26791, d249257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62382 q ha hb
    | true =>
      simp only [d26791, d249257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62383 q ha hb
  have h20 (q : Pattern) (ha : d26792 q = 1) (hb : d152855 q = 1) : d249258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26792, d249258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26792, d249258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d26793 q = 1) (hb : d152855 q = 1) : d249259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26793, d249259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d26793, d249259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d26795 q = 1) (hb : d152855 q = 1) : d249261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26795, d249261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62384 q ha hb
    | true =>
      simp only [d26795, d249261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62354 q ha hb
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202178 q = 1) : d249262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202178, d249262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d202178, d249262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d26801 q = 1) (hb : d152855 q = 1) : d249264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26801, d249264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62385 q ha hb
    | true =>
      simp only [d26801, d249264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d26802 q = 1) (hb : d152855 q = 1) : d249265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26802, d249265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d26802, d249265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d152855 q = 1) (hb : d202179 q = 1) : d249266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202179, d249266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202179, d249266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d152855 q = 1) (hb : d202180 q = 1) : d249267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202180, d249267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d202180, d249267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d152855 q = 1) (hb : d202181 q = 1) : d249268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202181, d249268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d202181, d249268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d152855 q = 1) (hb : d202182 q = 1) : d249269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202182, d249269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202182, d249269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro62387 (p : Pattern) (ha : d152855 p = 1) (hb : d202189 p = 1) : d249289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26795 q = 1) (hb : d152855 q = 1) : d249261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26795, d249261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62384 q ha hb
    | true =>
      simp only [d26795, d249261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62354 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202178 q = 1) : d249262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202178, d249262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202178, d249262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d26801 q = 1) (hb : d152855 q = 1) : d249264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26801, d249264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62385 q ha hb
    | true =>
      simp only [d26801, d249264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26802 q = 1) (hb : d152855 q = 1) : d249265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26802, d249265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26802, d249265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202179 q = 1) : d249266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202179, d249266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202179, d249266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202187 q = 1) : d249287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202187, d249287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202187, d249287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202188 q = 1) : d249288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202188, d249288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202188, d249288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202189 q = 1) : d249289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202189, d249289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202189, d249289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62388 (p : Pattern) (ha : d26852 p = 1) (hb : d152855 p = 1) : d249302 p = 1 := by
  have h0 (q : Pattern) (ha : d26837 q = 1) (hb : d152854 q = 1) : d26837 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26838 q = 1) (hb : d152854 q = 1) : d249297 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26838, d249297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26838, d249297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62342 q ha hb
  have h3 (q : Pattern) (ha : d26551 q = 1) (hb : d152854 q = 1) : d249125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26551, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62342 q ha hb
    | true =>
      simp only [d26551, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d26839 q = 1) (hb : d152854 q = 1) : d249298 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26839, d249298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26839, d249298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26552 q = 1) (hb : d152854 q = 1) : d249126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26552, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26552, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d26840 q = 1) (hb : d152854 q = 1) : d249299 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26840, d249299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26840, d249299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26841 q = 1) (hb : d152854 q = 1) : d249300 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26841, d249300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26841, d249300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d26842 q = 1) (hb : d152854 q = 1) : d249301 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26842, d249301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26842, d249301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d26851 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d26852 q = 1) (hb : d152855 q = 1) : d249302 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26852, d152855, d249302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26852, d152855, d249302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro62389 (p : Pattern) (ha : d26863 p = 1) (hb : d152855 p = 1) : d249308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26838 q = 1) (hb : d152854 q = 1) : d249297 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26838, d249297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26838, d249297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62342 q ha hb
  have h2 (q : Pattern) (ha : d26551 q = 1) (hb : d152854 q = 1) : d249125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26551, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62342 q ha hb
    | true =>
      simp only [d26551, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26839 q = 1) (hb : d152854 q = 1) : d249298 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26839, d249298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26839, d249298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26552 q = 1) (hb : d152854 q = 1) : d249126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26552, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26552, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26840 q = 1) (hb : d152854 q = 1) : d249299 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26840, d249299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26840, d249299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26841 q = 1) (hb : d152854 q = 1) : d249300 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26841, d249300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26841, d249300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26853 q = 1) (hb : d152854 q = 1) : d249303 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26853, d249303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26853, d249303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62343 q ha hb
  have h8 (q : Pattern) (ha : d26562 q = 1) (hb : d152854 q = 1) : d249130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26562, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62343 q ha hb
    | true =>
      simp only [d26562, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26854 q = 1) (hb : d152854 q = 1) : d249304 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26854, d249304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26854, d249304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26563 q = 1) (hb : d152854 q = 1) : d249131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26563, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26563, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26855 q = 1) (hb : d152854 q = 1) : d249305 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26855, d249305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26855, d249305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26856 q = 1) (hb : d152854 q = 1) : d249306 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26856, d249306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26856, d249306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26857 q = 1) (hb : d152854 q = 1) : d249307 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26857, d249307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26857, d249307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26862 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26863 q = 1) (hb : d152855 q = 1) : d249308 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26863, d152855, d249308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26863, d152855, d249308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62390 (p : Pattern) (ha : d26868 p = 1) (hb : d152855 p = 1) : d249317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26847 q = 1) (hb : d152854 q = 1) : d249303 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26847, d249303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26847, d249303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62370 q ha hb
  have h2 (q : Pattern) (ha : d26568 q = 1) (hb : d152854 q = 1) : d249130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62370 q ha hb
    | true =>
      simp only [d26568, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26848 q = 1) (hb : d152854 q = 1) : d249304 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26848, d249304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26848, d249304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26569 q = 1) (hb : d152854 q = 1) : d249131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26569, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26849 q = 1) (hb : d152854 q = 1) : d249305 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26849, d249305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26849, d249305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26850 q = 1) (hb : d152854 q = 1) : d249306 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26850, d249306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26850, d249306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26858 q = 1) (hb : d152854 q = 1) : d249312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26858, d249312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26858, d249312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
  have h8 (q : Pattern) (ha : d26575 q = 1) (hb : d152854 q = 1) : d249142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
    | true =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26859 q = 1) (hb : d152854 q = 1) : d249313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26859, d249313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26859, d249313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26576 q = 1) (hb : d152854 q = 1) : d249143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26860 q = 1) (hb : d152854 q = 1) : d249314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26860, d249314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26860, d249314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26861 q = 1) (hb : d152854 q = 1) : d249315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26861, d249315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26861, d249315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26862 q = 1) (hb : d152854 q = 1) : d249316 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26862, d249316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26862, d249316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26867 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26868 q = 1) (hb : d152855 q = 1) : d249317 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26868, d152855, d249317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26868, d152855, d249317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62391 (p : Pattern) (ha : d26888 p = 1) (hb : d152855 p = 1) : d249338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26864 q = 1) (hb : d152855 q = 1) : d249309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26864, d249309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62388 q ha hb
    | true =>
      simp only [d26864, d249309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62389 q ha hb
  have h2 (q : Pattern) (ha : d26865 q = 1) (hb : d152855 q = 1) : d249310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26865, d249310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26865, d249310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26866 q = 1) (hb : d152855 q = 1) : d249311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26866, d249311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26866, d249311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26869 q = 1) (hb : d152855 q = 1) : d249318 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26869, d249318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62389 q ha hb
    | true =>
      simp only [d26869, d249318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62390 q ha hb
  have h5 (q : Pattern) (ha : d26870 q = 1) (hb : d152855 q = 1) : d249319 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26870, d249319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26870, d249319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26871 q = 1) (hb : d152855 q = 1) : d249320 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26871, d249320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26871, d249320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26872 q = 1) (hb : d152855 q = 1) : d249321 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26872, d249321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26872, d249321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26879 q = 1) (hb : d152855 q = 1) : d249328 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26879, d249328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62389 q ha hb
    | true =>
      simp only [d26879, d249328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62360 q ha hb
  have h9 (q : Pattern) (ha : d26880 q = 1) (hb : d152855 q = 1) : d249329 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26880, d249329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26880, d249329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26881 q = 1) (hb : d152855 q = 1) : d249330 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26881, d249330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26881, d249330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26883 q = 1) (hb : d152855 q = 1) : d249333 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26883, d249333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62360 q ha hb
    | true =>
      simp only [d26883, d249333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62361 q ha hb
  have h12 (q : Pattern) (ha : d26884 q = 1) (hb : d152855 q = 1) : d249334 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26884, d249334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26884, d249334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26885 q = 1) (hb : d152855 q = 1) : d249335 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26885, d249335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26885, d249335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26886 q = 1) (hb : d152855 q = 1) : d249336 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26886, d249336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26886, d249336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26887 q = 1) (hb : d152855 q = 1) : d249337 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26887, d249337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26887, d249337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d26888 q = 1) (hb : d152855 q = 1) : d249338 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26888, d249338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26888, d249338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62392 (p : Pattern) (ha : d26893 p = 1) (hb : d152855 p = 1) : d249343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26879 q = 1) (hb : d152855 q = 1) : d249328 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26879, d249328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62389 q ha hb
    | true =>
      simp only [d26879, d249328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62360 q ha hb
  have h2 (q : Pattern) (ha : d26880 q = 1) (hb : d152855 q = 1) : d249329 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26880, d249329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26880, d249329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26881 q = 1) (hb : d152855 q = 1) : d249330 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26881, d249330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26881, d249330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26883 q = 1) (hb : d152855 q = 1) : d249333 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26883, d249333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62360 q ha hb
    | true =>
      simp only [d26883, d249333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62361 q ha hb
  have h5 (q : Pattern) (ha : d26884 q = 1) (hb : d152855 q = 1) : d249334 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26884, d249334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26884, d249334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26885 q = 1) (hb : d152855 q = 1) : d249335 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26885, d249335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26885, d249335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26886 q = 1) (hb : d152855 q = 1) : d249336 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26886, d249336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26886, d249336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26891 q = 1) (hb : d152855 q = 1) : d249341 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26891, d249341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26891, d249341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26892 q = 1) (hb : d152855 q = 1) : d249342 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26892, d249342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26892, d249342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26893 q = 1) (hb : d152855 q = 1) : d249343 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26893, d249343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26893, d249343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62393 (p : Pattern) (ha : d26899 p = 1) (hb : d152855 p = 1) : d249349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26889 q = 1) (hb : d152855 q = 1) : d249339 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26889, d249339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62391 q ha hb
    | true =>
      simp only [d26889, d249339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26890 q = 1) (hb : d152855 q = 1) : d249340 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26890, d249340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26890, d249340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26894 q = 1) (hb : d152855 q = 1) : d249344 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26894, d249344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62392 q ha hb
    | true =>
      simp only [d26894, d249344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26895 q = 1) (hb : d152855 q = 1) : d249345 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26895, d249345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26895, d249345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26896 q = 1) (hb : d152855 q = 1) : d249346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26896, d249346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26896, d249346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26897 q = 1) (hb : d152855 q = 1) : d249347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26897, d249347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26897, d249347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26898 q = 1) (hb : d152855 q = 1) : d249348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26898, d249348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26898, d249348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26899 q = 1) (hb : d152855 q = 1) : d249349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26899, d249349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26899, d249349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62394 (p : Pattern) (ha : d26907 p = 1) (hb : d152855 p = 1) : d249357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26894 q = 1) (hb : d152855 q = 1) : d249344 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26894, d249344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62392 q ha hb
    | true =>
      simp only [d26894, d249344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26895 q = 1) (hb : d152855 q = 1) : d249345 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26895, d249345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26895, d249345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26902 q = 1) (hb : d152855 q = 1) : d249352 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26902, d249352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62362 q ha hb
    | true =>
      simp only [d26902, d249352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26903 q = 1) (hb : d152855 q = 1) : d249353 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26903, d249353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26903, d249353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26904 q = 1) (hb : d152855 q = 1) : d249354 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26904, d249354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26904, d249354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26905 q = 1) (hb : d152855 q = 1) : d249355 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26905, d249355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26905, d249355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26906 q = 1) (hb : d152855 q = 1) : d249356 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26906, d249356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26906, d249356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26907 q = 1) (hb : d152855 q = 1) : d249357 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26907, d249357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26907, d249357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62395 (p : Pattern) (ha : d26967 p = 1) (hb : d152855 p = 1) : d249327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26873 q = 1) (hb : d152854 q = 1) : d249322 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26873, d249322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26873, d249322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62346 q ha hb
  have h2 (q : Pattern) (ha : d26584 q = 1) (hb : d152854 q = 1) : d249137 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26584, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62346 q ha hb
    | true =>
      simp only [d26584, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26874 q = 1) (hb : d152854 q = 1) : d249323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26874, d249323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26874, d249323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26585 q = 1) (hb : d152854 q = 1) : d249138 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26585, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26585, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26875 q = 1) (hb : d152854 q = 1) : d249324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26875, d249324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26875, d249324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26876 q = 1) (hb : d152854 q = 1) : d249325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26876, d249325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26876, d249325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26858 q = 1) (hb : d152854 q = 1) : d249312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26858, d249312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26858, d249312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
  have h8 (q : Pattern) (ha : d26575 q = 1) (hb : d152854 q = 1) : d249142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62345 q ha hb
    | true =>
      simp only [d26575, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26859 q = 1) (hb : d152854 q = 1) : d249313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26859, d249313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26859, d249313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26576 q = 1) (hb : d152854 q = 1) : d249143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26576, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26860 q = 1) (hb : d152854 q = 1) : d249314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26860, d249314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26860, d249314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26861 q = 1) (hb : d152854 q = 1) : d249315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26861, d249315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26861, d249315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26877 q = 1) (hb : d152854 q = 1) : d249326 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26877, d249326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26877, d249326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26966 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26967 q = 1) (hb : d152855 q = 1) : d249327 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26967, d152855, d249327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26967, d152855, d249327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62396 (p : Pattern) (ha : d26968 p = 1) (hb : d152855 p = 1) : d157631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26962 q = 1) (hb : d152854 q = 1) : d157626 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26962, d157626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26962, d157626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62375 q ha hb
  have h2 (q : Pattern) (ha : d26758 q = 1) (hb : d152854 q = 1) : d157413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26758, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62375 q ha hb
    | true =>
      simp only [d26758, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26963 q = 1) (hb : d152854 q = 1) : d157627 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26963, d157627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26963, d157627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26759 q = 1) (hb : d152854 q = 1) : d157414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26759, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26759, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26964 q = 1) (hb : d152854 q = 1) : d157628 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26964, d157628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26964, d157628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26965 q = 1) (hb : d152854 q = 1) : d157629 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26965, d157629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26965, d157629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26966 q = 1) (hb : d152854 q = 1) : d157630 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26966, d157630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26966, d157630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d26968 q = 1) (hb : d152855 q = 1) : d157631 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26968, d152855, d157631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26968, d152855, d157631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62397 (p : Pattern) (ha : d26974 p = 1) (hb : d152855 p = 1) : d249365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26879 q = 1) (hb : d152855 q = 1) : d249328 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26879, d249328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62389 q ha hb
    | true =>
      simp only [d26879, d249328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62360 q ha hb
  have h2 (q : Pattern) (ha : d26880 q = 1) (hb : d152855 q = 1) : d249329 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26880, d249329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26880, d249329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26881 q = 1) (hb : d152855 q = 1) : d249330 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26881, d249330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26881, d249330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26883 q = 1) (hb : d152855 q = 1) : d249333 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26883, d249333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62360 q ha hb
    | true =>
      simp only [d26883, d249333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62361 q ha hb
  have h5 (q : Pattern) (ha : d26884 q = 1) (hb : d152855 q = 1) : d249334 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26884, d249334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26884, d249334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26885 q = 1) (hb : d152855 q = 1) : d249335 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26885, d249335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26885, d249335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26886 q = 1) (hb : d152855 q = 1) : d249336 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26886, d249336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26886, d249336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26969 q = 1) (hb : d152855 q = 1) : d249360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26969, d249360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62395 q ha hb
    | true =>
      simp only [d26969, d249360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62396 q ha hb
  have h9 (q : Pattern) (ha : d26970 q = 1) (hb : d152855 q = 1) : d249361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26970, d249361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26970, d249361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26971 q = 1) (hb : d152855 q = 1) : d249362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26971, d249362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26971, d249362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26972 q = 1) (hb : d152855 q = 1) : d249363 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26972, d249363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26972, d249363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26973 q = 1) (hb : d152855 q = 1) : d249364 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26973, d249364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26973, d249364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26974 q = 1) (hb : d152855 q = 1) : d249365 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26974, d249365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26974, d249365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro62398 (p : Pattern) (ha : d26980 p = 1) (hb : d152855 p = 1) : d249371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26975 q = 1) (hb : d152855 q = 1) : d249366 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26975, d249366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62397 q ha hb
    | true =>
      simp only [d26975, d249366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26976 q = 1) (hb : d152855 q = 1) : d249367 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26976, d249367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26976, d249367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26977 q = 1) (hb : d152855 q = 1) : d249368 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26977, d249368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26977, d249368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26978 q = 1) (hb : d152855 q = 1) : d249369 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26978, d249369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26978, d249369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26979 q = 1) (hb : d152855 q = 1) : d249370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26979, d249370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26979, d249370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26980 q = 1) (hb : d152855 q = 1) : d249371 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26980, d249371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26980, d249371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62399 (p : Pattern) (ha : d152855 p = 1) (hb : d202199 p = 1) : d249377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26908 q = 1) (hb : d152855 q = 1) : d249358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26908, d249358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62393 q ha hb
    | true =>
      simp only [d26908, d249358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62394 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202195 q = 1) : d249359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202195, d249359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202195, d249359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d26981 q = 1) (hb : d152855 q = 1) : d249372 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26981, d249372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62398 q ha hb
    | true =>
      simp only [d26981, d249372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26982 q = 1) (hb : d152855 q = 1) : d249373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26982, d249373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26982, d249373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202196 q = 1) : d249374 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202196, d249374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202196, d249374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202197 q = 1) : d249375 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202197, d249375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202197, d249375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202198 q = 1) : d249376 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202198, d249376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202198, d249376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202199 q = 1) : d249377 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202199, d249377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202199, d249377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62400 (p : Pattern) (ha : d152855 p = 1) (hb : d202205 p = 1) : d249394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26622 q = 1) (hb : d152855 q = 1) : d249180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26622, d249180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26622, d249180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62353 q ha hb
  have h2 (q : Pattern) (ha : d26623 q = 1) (hb : d152855 q = 1) : d249181 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26623, d249181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26623, d249181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26632 q = 1) (hb : d152855 q = 1) : d249190 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26632, d249190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62353 q ha hb
    | true =>
      simp only [d26632, d249190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62356 q ha hb
  have h4 (q : Pattern) (ha : d26633 q = 1) (hb : d152855 q = 1) : d249191 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26633, d249191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26633, d249191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26634 q = 1) (hb : d152855 q = 1) : d249192 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d26634, d249192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26634, d249192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202183 q = 1) : d249270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202183, d249270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62379 q ha hb
    | true =>
      simp only [d202183, d249270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62386 q ha hb
  have h7 (q : Pattern) (ha : d26820 q = 1) (hb : d152855 q = 1) : d249283 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26820, d249283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62357 q ha hb
    | true =>
      simp only [d26820, d249283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62358 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202184 q = 1) : d249284 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202184, d249284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202184, d249284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202185 q = 1) : d249285 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202185, d249285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202185, d249285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d202186 q = 1) : d249286 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202186, d249286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d202186, d249286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d202190 q = 1) : d249290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202190, d249290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202190, d249290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62387 q ha hb
  have h12 (q : Pattern) (ha : d26829 q = 1) (hb : d152855 q = 1) : d249292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26829, d249292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26829, d249292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62359 q ha hb
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202191 q = 1) : d249293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202191, d249293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202191, d249293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202192 q = 1) : d249294 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202192, d249294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202192, d249294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202193 q = 1) : d249295 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202193, d249295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202193, d249295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d152855 q = 1) (hb : d202194 q = 1) : d249296 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202194, d249296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202194, d249296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d152855 q = 1) (hb : d202200 q = 1) : d249378 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202200, d249378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202200, d249378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62399 q ha hb
  have h18 (q : Pattern) (ha : d26998 q = 1) (hb : d152855 q = 1) : d249389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26998, d249389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26998, d249389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62364 q ha hb
  have h19 (q : Pattern) (ha : d152855 q = 1) (hb : d202201 q = 1) : d249390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202201, d249390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202201, d249390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d152855 q = 1) (hb : d202202 q = 1) : d249391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202202, d249391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202202, d249391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d152855 q = 1) (hb : d202203 q = 1) : d249392 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202203, d249392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202203, d249392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d152855 q = 1) (hb : d202204 q = 1) : d249393 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202204, d249393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202204, d249393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202205 q = 1) : d249394 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202205, d249394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202205, d249394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62401 (p : Pattern) (ha : d152855 p = 1) (hb : d202211 p = 1) : d249400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202206 q = 1) : d249395 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202206, d249395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202206, d249395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62400 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202207 q = 1) : d249396 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202207, d249396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202207, d249396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202208 q = 1) : d249397 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202208, d249397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202208, d249397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202209 q = 1) : d249398 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202209, d249398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202209, d249398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202210 q = 1) : d249399 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202210, d249399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202210, d249399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202211 q = 1) : d249400 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202211, d249400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202211, d249400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62402 (p : Pattern) (ha : d27019 p = 1) (hb : d152854 p = 1) : d249405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10351 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5717 q = 1) (hb : d152852 q = 1) : d5717 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27019 q = 1) (hb : d152854 q = 1) : d249405 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27019, d152854, d249405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d27019, d152854, d249405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62403 (p : Pattern) (ha : d27031 p = 1) (hb : d152855 p = 1) : d249411 p = 1 := by
  have h0 (q : Pattern) (ha : d27018 q = 1) (hb : d152854 q = 1) : d27018 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27020 q = 1) (hb : d152854 q = 1) : d249406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
    | true =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27021 q = 1) (hb : d152854 q = 1) : d249407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27022 q = 1) (hb : d152854 q = 1) : d249408 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27022, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27023 q = 1) (hb : d152854 q = 1) : d249409 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27023, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d27024 q = 1) (hb : d152854 q = 1) : d249410 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27024, d249410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27024, d249410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d27030 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d27031 q = 1) (hb : d152855 q = 1) : d249411 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27031, d152855, d249411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27031, d152855, d249411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62404 (p : Pattern) (ha : d27035 p = 1) (hb : d152854 p = 1) : d249412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10410 q = 1) (hb : d152852 q = 1) : d10410 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27035 q = 1) (hb : d152854 q = 1) : d249412 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27035, d152854, d249412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d27035, d152854, d249412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62405 (p : Pattern) (ha : d27042 p = 1) (hb : d152855 p = 1) : d249418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27020 q = 1) (hb : d152854 q = 1) : d249406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
    | true =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27021 q = 1) (hb : d152854 q = 1) : d249407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27022 q = 1) (hb : d152854 q = 1) : d249408 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27022, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27023 q = 1) (hb : d152854 q = 1) : d249409 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27023, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27036 q = 1) (hb : d152854 q = 1) : d249413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62404 q ha hb
    | true =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27037 q = 1) (hb : d152854 q = 1) : d249414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27038 q = 1) (hb : d152854 q = 1) : d249415 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27038, d249415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27038, d249415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27039 q = 1) (hb : d152854 q = 1) : d249416 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27039, d249416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27039, d249416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27040 q = 1) (hb : d152854 q = 1) : d249417 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27040, d249417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27040, d249417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d27041 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d27042 q = 1) (hb : d152855 q = 1) : d249418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27042, d152855, d249418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27042, d152855, d249418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62406 (p : Pattern) (ha : d27047 p = 1) (hb : d152855 p = 1) : d249423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27036 q = 1) (hb : d152854 q = 1) : d249413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62404 q ha hb
    | true =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27037 q = 1) (hb : d152854 q = 1) : d249414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27038 q = 1) (hb : d152854 q = 1) : d249415 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27038, d249415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27038, d249415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27039 q = 1) (hb : d152854 q = 1) : d249416 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27039, d249416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27039, d249416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27046 q = 1) (hb : d152854 q = 1) : d249422 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27046, d249422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27046, d249422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15557 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d27047 q = 1) (hb : d152855 q = 1) : d249423 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27047, d152855, d249423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27047, d152855, d249423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62407 (p : Pattern) (ha : d27054 p = 1) (hb : d152855 p = 1) : d249430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27043 q = 1) (hb : d152855 q = 1) : d249419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27043, d249419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62403 q ha hb
    | true =>
      simp only [d27043, d249419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62405 q ha hb
  have h2 (q : Pattern) (ha : d27044 q = 1) (hb : d152855 q = 1) : d249420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27044, d249420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27044, d249420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27045 q = 1) (hb : d152855 q = 1) : d249421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27045, d249421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27045, d249421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27048 q = 1) (hb : d152855 q = 1) : d249424 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27048, d249424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62405 q ha hb
    | true =>
      simp only [d27048, d249424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62406 q ha hb
  have h5 (q : Pattern) (ha : d27049 q = 1) (hb : d152855 q = 1) : d249425 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27049, d249425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27049, d249425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27050 q = 1) (hb : d152855 q = 1) : d249426 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27050, d249426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27050, d249426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27051 q = 1) (hb : d152855 q = 1) : d249427 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27051, d249427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27051, d249427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27052 q = 1) (hb : d152855 q = 1) : d249428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27052, d249428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27052, d249428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27053 q = 1) (hb : d152855 q = 1) : d249429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27053, d249429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27053, d249429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27054 q = 1) (hb : d152855 q = 1) : d249430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27054, d249430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27054, d249430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62408 (p : Pattern) (ha : d27058 p = 1) (hb : d152855 p = 1) : d249434 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27048 q = 1) (hb : d152855 q = 1) : d249424 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27048, d249424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62405 q ha hb
    | true =>
      simp only [d27048, d249424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62406 q ha hb
  have h2 (q : Pattern) (ha : d27049 q = 1) (hb : d152855 q = 1) : d249425 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27049, d249425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27049, d249425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27050 q = 1) (hb : d152855 q = 1) : d249426 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27050, d249426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27050, d249426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27052 q = 1) (hb : d152855 q = 1) : d249428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27052, d249428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27052, d249428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27057 q = 1) (hb : d152855 q = 1) : d249433 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27057, d249433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27057, d249433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27058 q = 1) (hb : d152855 q = 1) : d249434 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27058, d249434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27058, d249434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62409 (p : Pattern) (ha : d27064 p = 1) (hb : d152855 p = 1) : d249440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d152855 q = 1) : d249431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62407 q ha hb
    | true =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d152855 q = 1) : d249432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d152855 q = 1) : d249437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27062 q = 1) (hb : d152855 q = 1) : d249438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27062, d249438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27062, d249438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27063 q = 1) (hb : d152855 q = 1) : d249439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27063, d249439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27063, d249439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27064 q = 1) (hb : d152855 q = 1) : d249440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27064, d249440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27064, d249440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62410 (p : Pattern) (ha : d27068 p = 1) (hb : d152855 p = 1) : d249444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d152855 q = 1) : d249441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27066 q = 1) (hb : d152855 q = 1) : d249442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27066, d249442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27066, d249442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27067 q = 1) (hb : d152855 q = 1) : d249443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27067, d249443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27067, d249443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27068 q = 1) (hb : d152855 q = 1) : d249444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27068, d249444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27068, d249444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62411 (p : Pattern) (ha : d27074 p = 1) (hb : d152855 p = 1) : d249450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27069 q = 1) (hb : d152855 q = 1) : d249445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27069, d249445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62409 q ha hb
    | true =>
      simp only [d27069, d249445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62410 q ha hb
  have h2 (q : Pattern) (ha : d27070 q = 1) (hb : d152855 q = 1) : d249446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27070, d249446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27070, d249446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27071 q = 1) (hb : d152855 q = 1) : d249447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27071, d249447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27071, d249447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27072 q = 1) (hb : d152855 q = 1) : d249448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27072, d249448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27072, d249448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27073 q = 1) (hb : d152855 q = 1) : d249449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27073, d249449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27073, d249449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27074 q = 1) (hb : d152855 q = 1) : d249450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27074, d249450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27074, d249450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62412 (p : Pattern) (ha : d27077 p = 1) (hb : d152855 p = 1) : d249453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d152855 q = 1) : d249431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62407 q ha hb
    | true =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d152855 q = 1) : d249432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d152855 q = 1) : d249437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27062 q = 1) (hb : d152855 q = 1) : d249438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27062, d249438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27062, d249438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27063 q = 1) (hb : d152855 q = 1) : d249439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27063, d249439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27063, d249439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27077 q = 1) (hb : d152855 q = 1) : d249453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27077, d249453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27077, d249453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62413 (p : Pattern) (ha : d27078 p = 1) (hb : d152855 p = 1) : d249454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d152855 q = 1) : d249441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27066 q = 1) (hb : d152855 q = 1) : d249442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27066, d249442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27066, d249442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27067 q = 1) (hb : d152855 q = 1) : d249443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27067, d249443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27067, d249443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27078 q = 1) (hb : d152855 q = 1) : d249454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27078, d249454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27078, d249454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62414 (p : Pattern) (ha : d27084 p = 1) (hb : d152855 p = 1) : d249460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27069 q = 1) (hb : d152855 q = 1) : d249445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27069, d249445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62409 q ha hb
    | true =>
      simp only [d27069, d249445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62410 q ha hb
  have h2 (q : Pattern) (ha : d27070 q = 1) (hb : d152855 q = 1) : d249446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27070, d249446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27070, d249446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27071 q = 1) (hb : d152855 q = 1) : d249447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27071, d249447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27071, d249447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27072 q = 1) (hb : d152855 q = 1) : d249448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27072, d249448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27072, d249448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27073 q = 1) (hb : d152855 q = 1) : d249449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27073, d249449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27073, d249449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27079 q = 1) (hb : d152855 q = 1) : d249455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27079, d249455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62412 q ha hb
    | true =>
      simp only [d27079, d249455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62413 q ha hb
  have h7 (q : Pattern) (ha : d27080 q = 1) (hb : d152855 q = 1) : d249456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27080, d249456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27080, d249456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27081 q = 1) (hb : d152855 q = 1) : d249457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27081, d249457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27081, d249457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27082 q = 1) (hb : d152855 q = 1) : d249458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27082, d249458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27082, d249458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27083 q = 1) (hb : d152855 q = 1) : d249459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27083, d249459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27083, d249459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27084 q = 1) (hb : d152855 q = 1) : d249460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27084, d249460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27084, d249460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62415 (p : Pattern) (ha : d27246 p = 1) (hb : d152855 p = 1) : d249540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27069 q = 1) (hb : d152855 q = 1) : d249445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27069, d249445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62409 q ha hb
    | true =>
      simp only [d27069, d249445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62410 q ha hb
  have h2 (q : Pattern) (ha : d27070 q = 1) (hb : d152855 q = 1) : d249446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27070, d249446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27070, d249446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27071 q = 1) (hb : d152855 q = 1) : d249447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27071, d249447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27071, d249447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27072 q = 1) (hb : d152855 q = 1) : d249448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27072, d249448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27072, d249448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27073 q = 1) (hb : d152855 q = 1) : d249449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27073, d249449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27073, d249449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27241 q = 1) (hb : d152855 q = 1) : d249535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27241, d249535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62410 q ha hb
    | true =>
      simp only [d27241, d249535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27242 q = 1) (hb : d152855 q = 1) : d249536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27242, d249536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27242, d249536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27243 q = 1) (hb : d152855 q = 1) : d249537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27243, d249537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27243, d249537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27244 q = 1) (hb : d152855 q = 1) : d249538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27244, d249538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27244, d249538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27245 q = 1) (hb : d152855 q = 1) : d249539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27245, d249539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27245, d249539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27246 q = 1) (hb : d152855 q = 1) : d249540 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27246, d249540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27246, d249540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62416 (p : Pattern) (ha : d27252 p = 1) (hb : d152855 p = 1) : d249546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27241 q = 1) (hb : d152855 q = 1) : d249535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27241, d249535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62410 q ha hb
    | true =>
      simp only [d27241, d249535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27242 q = 1) (hb : d152855 q = 1) : d249536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27242, d249536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27242, d249536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27243 q = 1) (hb : d152855 q = 1) : d249537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27243, d249537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27243, d249537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27244 q = 1) (hb : d152855 q = 1) : d249538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27244, d249538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27244, d249538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27245 q = 1) (hb : d152855 q = 1) : d249539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27245, d249539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27245, d249539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27247 q = 1) (hb : d152855 q = 1) : d249541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27247, d249541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62413 q ha hb
    | true =>
      simp only [d27247, d249541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27248 q = 1) (hb : d152855 q = 1) : d249542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27248, d249542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27248, d249542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27249 q = 1) (hb : d152855 q = 1) : d249543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27249, d249543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27249, d249543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27250 q = 1) (hb : d152855 q = 1) : d249544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27250, d249544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27250, d249544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27251 q = 1) (hb : d152855 q = 1) : d249545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27251, d249545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27251, d249545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27252 q = 1) (hb : d152855 q = 1) : d249546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27252, d249546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27252, d249546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62417 (p : Pattern) (ha : d27261 p = 1) (hb : d152855 p = 1) : d249555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27247 q = 1) (hb : d152855 q = 1) : d249541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27247, d249541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62413 q ha hb
    | true =>
      simp only [d27247, d249541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27248 q = 1) (hb : d152855 q = 1) : d249542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27248, d249542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27248, d249542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27249 q = 1) (hb : d152855 q = 1) : d249543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27249, d249543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27249, d249543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27250 q = 1) (hb : d152855 q = 1) : d249544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27250, d249544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27250, d249544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27251 q = 1) (hb : d152855 q = 1) : d249545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27251, d249545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27251, d249545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27261 q = 1) (hb : d152855 q = 1) : d249555 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27261, d249555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27261, d249555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62418 (p : Pattern) (ha : d27298 p = 1) (hb : d152855 p = 1) : d249575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27272 q = 1) (hb : d152854 q = 1) : d249561 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
  have h2 (q : Pattern) (ha : d27020 q = 1) (hb : d152854 q = 1) : d249406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
    | true =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27273 q = 1) (hb : d152854 q = 1) : d249562 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27273, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27021 q = 1) (hb : d152854 q = 1) : d249407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27274 q = 1) (hb : d152854 q = 1) : d249563 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27274, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27275 q = 1) (hb : d152854 q = 1) : d249564 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27275, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27293 q = 1) (hb : d152854 q = 1) : d249570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27293, d249570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27293, d249570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62404 q ha hb
  have h8 (q : Pattern) (ha : d27036 q = 1) (hb : d152854 q = 1) : d249413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62404 q ha hb
    | true =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27294 q = 1) (hb : d152854 q = 1) : d249571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27294, d249571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27294, d249571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27037 q = 1) (hb : d152854 q = 1) : d249414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27295 q = 1) (hb : d152854 q = 1) : d249572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27295, d249572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27295, d249572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27296 q = 1) (hb : d152854 q = 1) : d249573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27296, d249573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27296, d249573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d27297 q = 1) (hb : d152854 q = 1) : d249574 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27297, d249574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27297, d249574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27287 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d27298 q = 1) (hb : d152855 q = 1) : d249575 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27298, d152855, d249575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d27298, d152855, d249575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62419 (p : Pattern) (ha : d27303 p = 1) (hb : d152855 p = 1) : d249581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27293 q = 1) (hb : d152854 q = 1) : d249570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27293, d249570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27293, d249570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62404 q ha hb
  have h2 (q : Pattern) (ha : d27036 q = 1) (hb : d152854 q = 1) : d249413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62404 q ha hb
    | true =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27294 q = 1) (hb : d152854 q = 1) : d249571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27294, d249571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27294, d249571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27037 q = 1) (hb : d152854 q = 1) : d249414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27295 q = 1) (hb : d152854 q = 1) : d249572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27295, d249572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27295, d249572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27296 q = 1) (hb : d152854 q = 1) : d249573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27296, d249573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27296, d249573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27302 q = 1) (hb : d152854 q = 1) : d249580 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27302, d249580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27302, d249580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15794 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d27303 q = 1) (hb : d152855 q = 1) : d249581 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27303, d152855, d249581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27303, d152855, d249581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62420 (p : Pattern) (ha : d27322 p = 1) (hb : d152855 p = 1) : d249600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27304 q = 1) (hb : d152855 q = 1) : d249582 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27304, d249582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62418 q ha hb
    | true =>
      simp only [d27304, d249582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62419 q ha hb
  have h2 (q : Pattern) (ha : d27305 q = 1) (hb : d152855 q = 1) : d249583 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27305, d249583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27305, d249583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27306 q = 1) (hb : d152855 q = 1) : d249584 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27306, d249584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27306, d249584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27312 q = 1) (hb : d152855 q = 1) : d249590 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27312, d249590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27312, d249590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27321 q = 1) (hb : d152855 q = 1) : d249599 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27321, d249599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27321, d249599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27322 q = 1) (hb : d152855 q = 1) : d249600 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27322, d249600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27322, d249600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62421 (p : Pattern) (ha : d27414 p = 1) (hb : d152855 p = 1) : d249631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27323 q = 1) (hb : d152855 q = 1) : d249601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27323, d249601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62420 q ha hb
    | true =>
      simp only [d27323, d249601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27324 q = 1) (hb : d152855 q = 1) : d249602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27324, d249602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27324, d249602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27411 q = 1) (hb : d152855 q = 1) : d249628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27411, d249628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27411, d249628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27412 q = 1) (hb : d152855 q = 1) : d249629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27412, d249629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27412, d249629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27413 q = 1) (hb : d152855 q = 1) : d249630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27413, d249630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27413, d249630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27414 q = 1) (hb : d152855 q = 1) : d249631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27414, d249631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27414, d249631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62422 (p : Pattern) (ha : d27420 p = 1) (hb : d152855 p = 1) : d249637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27415 q = 1) (hb : d152855 q = 1) : d249632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27415, d249632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62421 q ha hb
    | true =>
      simp only [d27415, d249632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27416 q = 1) (hb : d152855 q = 1) : d249633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27416, d249633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27416, d249633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27417 q = 1) (hb : d152855 q = 1) : d249634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27417, d249634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27417, d249634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27418 q = 1) (hb : d152855 q = 1) : d249635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27418, d249635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27418, d249635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27419 q = 1) (hb : d152855 q = 1) : d249636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27419, d249636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27419, d249636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27420 q = 1) (hb : d152855 q = 1) : d249637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27420, d249637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27420, d249637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62423 (p : Pattern) (ha : d27089 p = 1) (hb : d152855 p = 1) : d249465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d152855 q = 1) : d249431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62407 q ha hb
    | true =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d152855 q = 1) : d249432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d152855 q = 1) : d249437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27062 q = 1) (hb : d152855 q = 1) : d249438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27062, d249438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27062, d249438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27088 q = 1) (hb : d152855 q = 1) : d249464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27088, d249464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27088, d249464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27089 q = 1) (hb : d152855 q = 1) : d249465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27089, d249465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27089, d249465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62424 (p : Pattern) (ha : d27091 p = 1) (hb : d152855 p = 1) : d249467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d152855 q = 1) : d249441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27066 q = 1) (hb : d152855 q = 1) : d249442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27066, d249442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27066, d249442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27090 q = 1) (hb : d152855 q = 1) : d249466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27090, d249466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27090, d249466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27091 q = 1) (hb : d152855 q = 1) : d249467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27091, d249467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27091, d249467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62425 (p : Pattern) (ha : d27098 p = 1) (hb : d152855 p = 1) : d249474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d152855 q = 1) : d249431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62407 q ha hb
    | true =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d152855 q = 1) : d249432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d152855 q = 1) : d249437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27096 q = 1) (hb : d152855 q = 1) : d249472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27096, d249472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27096, d249472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27097 q = 1) (hb : d152855 q = 1) : d249473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27097, d249473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27097, d249473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27098 q = 1) (hb : d152855 q = 1) : d249474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27098, d249474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27098, d249474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62426 (p : Pattern) (ha : d27101 p = 1) (hb : d152855 p = 1) : d249477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d152855 q = 1) : d249441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27099 q = 1) (hb : d152855 q = 1) : d249475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27099, d249475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27099, d249475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27100 q = 1) (hb : d152855 q = 1) : d249476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27100, d249476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27100, d249476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27101 q = 1) (hb : d152855 q = 1) : d249477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27101, d249477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27101, d249477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62427 (p : Pattern) (ha : d27106 p = 1) (hb : d152855 p = 1) : d157794 p = 1 := by
  have h0 (q : Pattern) (ha : d27105 q = 1) (hb : d152854 q = 1) : d27105 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27024 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27106 q = 1) (hb : d152855 q = 1) : d157794 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27106, d152855, d157794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27106, d152855, d157794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro62428 (p : Pattern) (ha : d27025 p = 1) (hb : d152854 p = 1) : d249412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10410 q = 1) (hb : d152852 q = 1) : d10410 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27025 q = 1) (hb : d152854 q = 1) : d249412 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27025, d152854, d249412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d27025, d152854, d249412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62429 (p : Pattern) (ha : d27110 p = 1) (hb : d152855 p = 1) : d249418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27020 q = 1) (hb : d152854 q = 1) : d249406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
    | true =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27021 q = 1) (hb : d152854 q = 1) : d249407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27022 q = 1) (hb : d152854 q = 1) : d249408 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27022, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27023 q = 1) (hb : d152854 q = 1) : d249409 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27023, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27026 q = 1) (hb : d152854 q = 1) : d249413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27026, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62428 q ha hb
    | true =>
      simp only [d27026, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27027 q = 1) (hb : d152854 q = 1) : d249414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27027, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27027, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27028 q = 1) (hb : d152854 q = 1) : d249415 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27028, d249415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27028, d249415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27029 q = 1) (hb : d152854 q = 1) : d249416 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27029, d249416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27029, d249416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27030 q = 1) (hb : d152854 q = 1) : d249417 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27030, d249417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27030, d249417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d27041 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d27110 q = 1) (hb : d152855 q = 1) : d249418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27110, d152855, d249418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27110, d152855, d249418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62430 (p : Pattern) (ha : d27116 p = 1) (hb : d152855 p = 1) : d249486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27107 q = 1) (hb : d152855 q = 1) : d249481 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27107, d249481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62427 q ha hb
    | true =>
      simp only [d27107, d249481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62403 q ha hb
  have h2 (q : Pattern) (ha : d27108 q = 1) (hb : d152855 q = 1) : d249482 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27108, d249482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27108, d249482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27109 q = 1) (hb : d152855 q = 1) : d249483 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27109, d249483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27109, d249483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27111 q = 1) (hb : d152855 q = 1) : d249419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27111, d249419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62403 q ha hb
    | true =>
      simp only [d27111, d249419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62429 q ha hb
  have h5 (q : Pattern) (ha : d27112 q = 1) (hb : d152855 q = 1) : d249420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27112, d249420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27112, d249420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27113 q = 1) (hb : d152855 q = 1) : d249421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27113, d249421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27113, d249421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27114 q = 1) (hb : d152855 q = 1) : d249484 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27114, d249484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27114, d249484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27043 q = 1) (hb : d152855 q = 1) : d249419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27043, d249419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62403 q ha hb
    | true =>
      simp only [d27043, d249419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62405 q ha hb
  have h9 (q : Pattern) (ha : d27044 q = 1) (hb : d152855 q = 1) : d249420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27044, d249420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27044, d249420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27045 q = 1) (hb : d152855 q = 1) : d249421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27045, d249421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27045, d249421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27048 q = 1) (hb : d152855 q = 1) : d249424 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27048, d249424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62405 q ha hb
    | true =>
      simp only [d27048, d249424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62406 q ha hb
  have h12 (q : Pattern) (ha : d27049 q = 1) (hb : d152855 q = 1) : d249425 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27049, d249425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27049, d249425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27050 q = 1) (hb : d152855 q = 1) : d249426 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27050, d249426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27050, d249426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d27051 q = 1) (hb : d152855 q = 1) : d249427 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27051, d249427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27051, d249427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27115 q = 1) (hb : d152855 q = 1) : d249485 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27115, d249485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27115, d249485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d27116 q = 1) (hb : d152855 q = 1) : d249486 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27116, d249486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d27116, d249486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62431 (p : Pattern) (ha : d27122 p = 1) (hb : d152855 p = 1) : d249492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27117 q = 1) (hb : d152855 q = 1) : d249487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27117, d249487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62430 q ha hb
    | true =>
      simp only [d27117, d249487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27118 q = 1) (hb : d152855 q = 1) : d249488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27118, d249488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27118, d249488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27055 q = 1) (hb : d152855 q = 1) : d249431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62407 q ha hb
    | true =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27056 q = 1) (hb : d152855 q = 1) : d249432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27119 q = 1) (hb : d152855 q = 1) : d249489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27119, d249489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27119, d249489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27120 q = 1) (hb : d152855 q = 1) : d249490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27120, d249490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27120, d249490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27121 q = 1) (hb : d152855 q = 1) : d249491 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27121, d249491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27121, d249491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27122 q = 1) (hb : d152855 q = 1) : d249492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27122, d249492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27122, d249492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62432 (p : Pattern) (ha : d27190 p = 1) (hb : d152855 p = 1) : d249418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27020 q = 1) (hb : d152854 q = 1) : d249406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
    | true =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27021 q = 1) (hb : d152854 q = 1) : d249407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27022 q = 1) (hb : d152854 q = 1) : d249408 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27022, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27023 q = 1) (hb : d152854 q = 1) : d249409 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27023, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27036 q = 1) (hb : d152854 q = 1) : d249413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62404 q ha hb
    | true =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27037 q = 1) (hb : d152854 q = 1) : d249414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27038 q = 1) (hb : d152854 q = 1) : d249415 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27038, d249415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27038, d249415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27039 q = 1) (hb : d152854 q = 1) : d249416 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27039, d249416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27039, d249416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27040 q = 1) (hb : d152854 q = 1) : d249417 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27040, d249417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27040, d249417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d27189 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d27190 q = 1) (hb : d152855 q = 1) : d249418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27190, d152855, d249418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27190, d152855, d249418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62433 (p : Pattern) (ha : d27191 p = 1) (hb : d152854 p = 1) : d157725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27183 q = 1) (hb : d152852 q = 1) : d27183 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27191 q = 1) (hb : d152854 q = 1) : d157725 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27191, d152854, d157725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d27191, d152854, d157725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62434 (p : Pattern) (ha : d27197 p = 1) (hb : d152855 p = 1) : d157731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27192 q = 1) (hb : d152854 q = 1) : d157726 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27192, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62433 q ha hb
    | true =>
      simp only [d27192, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27193 q = 1) (hb : d152854 q = 1) : d157727 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27193, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27193, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27194 q = 1) (hb : d152854 q = 1) : d157728 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27194, d157728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27194, d157728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27195 q = 1) (hb : d152854 q = 1) : d157729 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27195, d157729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27195, d157729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27196 q = 1) (hb : d152854 q = 1) : d157730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27196, d157730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27196, d157730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d27197 q = 1) (hb : d152855 q = 1) : d157731 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27197, d152855, d157731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27197, d152855, d157731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62435 (p : Pattern) (ha : d27203 p = 1) (hb : d152855 p = 1) : d249500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27043 q = 1) (hb : d152855 q = 1) : d249419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27043, d249419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62403 q ha hb
    | true =>
      simp only [d27043, d249419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62405 q ha hb
  have h2 (q : Pattern) (ha : d27044 q = 1) (hb : d152855 q = 1) : d249420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27044, d249420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27044, d249420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27045 q = 1) (hb : d152855 q = 1) : d249421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27045, d249421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27045, d249421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27048 q = 1) (hb : d152855 q = 1) : d249424 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27048, d249424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62405 q ha hb
    | true =>
      simp only [d27048, d249424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62406 q ha hb
  have h5 (q : Pattern) (ha : d27049 q = 1) (hb : d152855 q = 1) : d249425 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27049, d249425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27049, d249425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27050 q = 1) (hb : d152855 q = 1) : d249426 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27050, d249426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27050, d249426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27051 q = 1) (hb : d152855 q = 1) : d249427 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27051, d249427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27051, d249427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27198 q = 1) (hb : d152855 q = 1) : d249495 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27198, d249495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62432 q ha hb
    | true =>
      simp only [d27198, d249495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62434 q ha hb
  have h9 (q : Pattern) (ha : d27199 q = 1) (hb : d152855 q = 1) : d249496 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27199, d249496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27199, d249496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27200 q = 1) (hb : d152855 q = 1) : d249497 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27200, d249497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27200, d249497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27201 q = 1) (hb : d152855 q = 1) : d249498 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27201, d249498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27201, d249498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d27202 q = 1) (hb : d152855 q = 1) : d249499 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27202, d249499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27202, d249499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27203 q = 1) (hb : d152855 q = 1) : d249500 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27203, d249500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d27203, d249500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro62436 (p : Pattern) (ha : d27209 p = 1) (hb : d152855 p = 1) : d249506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27204 q = 1) (hb : d152855 q = 1) : d249501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27204, d249501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62435 q ha hb
    | true =>
      simp only [d27204, d249501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27205 q = 1) (hb : d152855 q = 1) : d249502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27205, d249502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27205, d249502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27206 q = 1) (hb : d152855 q = 1) : d249503 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27206, d249503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27206, d249503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27207 q = 1) (hb : d152855 q = 1) : d249504 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27207, d249504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27207, d249504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27208 q = 1) (hb : d152855 q = 1) : d249505 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27208, d249505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27208, d249505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27209 q = 1) (hb : d152855 q = 1) : d249506 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27209, d249506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27209, d249506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62437 (p : Pattern) (ha : d152855 p = 1) (hb : d202220 p = 1) : d249512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27092 q = 1) (hb : d152855 q = 1) : d249468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27092, d249468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62423 q ha hb
    | true =>
      simp only [d27092, d249468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62424 q ha hb
  have h2 (q : Pattern) (ha : d27093 q = 1) (hb : d152855 q = 1) : d249469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27093, d249469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27093, d249469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27094 q = 1) (hb : d152855 q = 1) : d249470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27094, d249470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27094, d249470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27095 q = 1) (hb : d152855 q = 1) : d249471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27095, d249471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27095, d249471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27102 q = 1) (hb : d152855 q = 1) : d249478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27102, d249478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62425 q ha hb
    | true =>
      simp only [d27102, d249478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62426 q ha hb
  have h6 (q : Pattern) (ha : d27103 q = 1) (hb : d152855 q = 1) : d249479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27103, d249479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27103, d249479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27104 q = 1) (hb : d152855 q = 1) : d249480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27104, d249480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27104, d249480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27123 q = 1) (hb : d152855 q = 1) : d249493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27123, d249493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62431 q ha hb
    | true =>
      simp only [d27123, d249493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62409 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202216 q = 1) : d249494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202216, d249494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202216, d249494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d27210 q = 1) (hb : d152855 q = 1) : d249507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27210, d249507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62436 q ha hb
    | true =>
      simp only [d27210, d249507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27211 q = 1) (hb : d152855 q = 1) : d249508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27211, d249508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27211, d249508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202217 q = 1) : d249509 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202217, d249509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202217, d249509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202218 q = 1) : d249510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202218, d249510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202218, d249510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202219 q = 1) : d249511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202219, d249511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202219, d249511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202220 q = 1) : d249512 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202220, d249512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202220, d249512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62438 (p : Pattern) (ha : d27216 p = 1) (hb : d152855 p = 1) : d249513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d152855 q = 1) : d249431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62407 q ha hb
    | true =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d152855 q = 1) : d249432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d152855 q = 1) : d249437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27062 q = 1) (hb : d152855 q = 1) : d249438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27062, d249438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27062, d249438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27088 q = 1) (hb : d152855 q = 1) : d249464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27088, d249464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27088, d249464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27216 q = 1) (hb : d152855 q = 1) : d249513 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27216, d249513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27216, d249513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62439 (p : Pattern) (ha : d27217 p = 1) (hb : d152855 p = 1) : d249514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d152855 q = 1) : d249441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27066 q = 1) (hb : d152855 q = 1) : d249442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27066, d249442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27066, d249442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27090 q = 1) (hb : d152855 q = 1) : d249466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27090, d249466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27090, d249466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27217 q = 1) (hb : d152855 q = 1) : d249514 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27217, d249514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27217, d249514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62440 (p : Pattern) (ha : d27222 p = 1) (hb : d152855 p = 1) : d249519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d152855 q = 1) : d249431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62407 q ha hb
    | true =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d152855 q = 1) : d249432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d152855 q = 1) : d249437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d249437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27096 q = 1) (hb : d152855 q = 1) : d249472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27096, d249472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27096, d249472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27097 q = 1) (hb : d152855 q = 1) : d249473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27097, d249473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27097, d249473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27222 q = 1) (hb : d152855 q = 1) : d249519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27222, d249519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27222, d249519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62441 (p : Pattern) (ha : d27223 p = 1) (hb : d152855 p = 1) : d249520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d152855 q = 1) : d249435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62408 q ha hb
    | true =>
      simp only [d27059, d249435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d152855 q = 1) : d249436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d249436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d152855 q = 1) : d249441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d249441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27099 q = 1) (hb : d152855 q = 1) : d249475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27099, d249475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27099, d249475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27100 q = 1) (hb : d152855 q = 1) : d249476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27100, d249476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27100, d249476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27223 q = 1) (hb : d152855 q = 1) : d249520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27223, d249520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27223, d249520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62442 (p : Pattern) (ha : d27227 p = 1) (hb : d152855 p = 1) : d249524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27117 q = 1) (hb : d152855 q = 1) : d249487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27117, d249487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62430 q ha hb
    | true =>
      simp only [d27117, d249487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27118 q = 1) (hb : d152855 q = 1) : d249488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27118, d249488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27118, d249488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27055 q = 1) (hb : d152855 q = 1) : d249431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62407 q ha hb
    | true =>
      simp only [d27055, d249431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27056 q = 1) (hb : d152855 q = 1) : d249432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d249432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27119 q = 1) (hb : d152855 q = 1) : d249489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27119, d249489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27119, d249489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27120 q = 1) (hb : d152855 q = 1) : d249490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27120, d249490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27120, d249490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27121 q = 1) (hb : d152855 q = 1) : d249491 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27121, d249491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27121, d249491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27227 q = 1) (hb : d152855 q = 1) : d249524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27227, d249524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27227, d249524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62443 (p : Pattern) (ha : d27233 p = 1) (hb : d152855 p = 1) : d249527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27204 q = 1) (hb : d152855 q = 1) : d249501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27204, d249501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62435 q ha hb
    | true =>
      simp only [d27204, d249501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27205 q = 1) (hb : d152855 q = 1) : d249502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27205, d249502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27205, d249502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27206 q = 1) (hb : d152855 q = 1) : d249503 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27206, d249503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27206, d249503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27207 q = 1) (hb : d152855 q = 1) : d249504 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27207, d249504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27207, d249504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27208 q = 1) (hb : d152855 q = 1) : d249505 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27208, d249505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27208, d249505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27233 q = 1) (hb : d152855 q = 1) : d249527 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27233, d249527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27233, d249527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62444 (p : Pattern) (ha : d152855 p = 1) (hb : d202225 p = 1) : d249533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27092 q = 1) (hb : d152855 q = 1) : d249468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27092, d249468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62423 q ha hb
    | true =>
      simp only [d27092, d249468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62424 q ha hb
  have h2 (q : Pattern) (ha : d27093 q = 1) (hb : d152855 q = 1) : d249469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27093, d249469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27093, d249469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27094 q = 1) (hb : d152855 q = 1) : d249470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27094, d249470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27094, d249470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27095 q = 1) (hb : d152855 q = 1) : d249471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27095, d249471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27095, d249471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27102 q = 1) (hb : d152855 q = 1) : d249478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27102, d249478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62425 q ha hb
    | true =>
      simp only [d27102, d249478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62426 q ha hb
  have h6 (q : Pattern) (ha : d27103 q = 1) (hb : d152855 q = 1) : d249479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27103, d249479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27103, d249479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27104 q = 1) (hb : d152855 q = 1) : d249480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27104, d249480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27104, d249480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27123 q = 1) (hb : d152855 q = 1) : d249493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27123, d249493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62431 q ha hb
    | true =>
      simp only [d27123, d249493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62409 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202216 q = 1) : d249494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202216, d249494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202216, d249494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d27210 q = 1) (hb : d152855 q = 1) : d249507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27210, d249507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62436 q ha hb
    | true =>
      simp only [d27210, d249507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27211 q = 1) (hb : d152855 q = 1) : d249508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27211, d249508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27211, d249508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202217 q = 1) : d249509 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202217, d249509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202217, d249509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202218 q = 1) : d249510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202218, d249510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202218, d249510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202219 q = 1) : d249511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202219, d249511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202219, d249511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27218 q = 1) (hb : d152855 q = 1) : d249515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27218, d249515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62438 q ha hb
    | true =>
      simp only [d27218, d249515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62439 q ha hb
  have h16 (q : Pattern) (ha : d27219 q = 1) (hb : d152855 q = 1) : d249516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27219, d249516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27219, d249516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d27220 q = 1) (hb : d152855 q = 1) : d249517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27220, d249517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d27220, d249517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d27221 q = 1) (hb : d152855 q = 1) : d249518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27221, d249518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27221, d249518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d27224 q = 1) (hb : d152855 q = 1) : d249521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27224, d249521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62440 q ha hb
    | true =>
      simp only [d27224, d249521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62441 q ha hb
  have h20 (q : Pattern) (ha : d27225 q = 1) (hb : d152855 q = 1) : d249522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27225, d249522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27225, d249522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d27226 q = 1) (hb : d152855 q = 1) : d249523 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27226, d249523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d27226, d249523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d27228 q = 1) (hb : d152855 q = 1) : d249525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27228, d249525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62442 q ha hb
    | true =>
      simp only [d27228, d249525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62412 q ha hb
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202221 q = 1) : d249526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202221, d249526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d202221, d249526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d27234 q = 1) (hb : d152855 q = 1) : d249528 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27234, d249528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62443 q ha hb
    | true =>
      simp only [d27234, d249528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d27235 q = 1) (hb : d152855 q = 1) : d249529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27235, d249529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d27235, d249529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d152855 q = 1) (hb : d202222 q = 1) : d249530 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202222, d249530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202222, d249530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d152855 q = 1) (hb : d202223 q = 1) : d249531 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202223, d249531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d202223, d249531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d152855 q = 1) (hb : d202224 q = 1) : d249532 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202224, d249532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d202224, d249532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d152855 q = 1) (hb : d202225 q = 1) : d249533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202225, d249533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202225, d249533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro62445 (p : Pattern) (ha : d152855 p = 1) (hb : d202232 p = 1) : d249553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27228 q = 1) (hb : d152855 q = 1) : d249525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27228, d249525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62442 q ha hb
    | true =>
      simp only [d27228, d249525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62412 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202221 q = 1) : d249526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202221, d249526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202221, d249526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d27234 q = 1) (hb : d152855 q = 1) : d249528 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27234, d249528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62443 q ha hb
    | true =>
      simp only [d27234, d249528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27235 q = 1) (hb : d152855 q = 1) : d249529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27235, d249529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27235, d249529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202222 q = 1) : d249530 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202222, d249530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202222, d249530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202230 q = 1) : d249551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202230, d249551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202230, d249551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202231 q = 1) : d249552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202231, d249552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202231, d249552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202232 q = 1) : d249553 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202232, d249553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202232, d249553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62446 (p : Pattern) (ha : d27277 p = 1) (hb : d152855 p = 1) : d157885 p = 1 := by
  have h0 (q : Pattern) (ha : d27271 q = 1) (hb : d152854 q = 1) : d27271 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27277 q = 1) (hb : d152855 q = 1) : d157885 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27277, d152855, d157885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27277, d152855, d157885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro62447 (p : Pattern) (ha : d27283 p = 1) (hb : d152855 p = 1) : d249566 p = 1 := by
  have h0 (q : Pattern) (ha : d27270 q = 1) (hb : d152854 q = 1) : d27270 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27272 q = 1) (hb : d152854 q = 1) : d249561 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27272, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
  have h3 (q : Pattern) (ha : d27020 q = 1) (hb : d152854 q = 1) : d249406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
    | true =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27273 q = 1) (hb : d152854 q = 1) : d249562 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27273, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27021 q = 1) (hb : d152854 q = 1) : d249407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d27274 q = 1) (hb : d152854 q = 1) : d249563 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27274, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27275 q = 1) (hb : d152854 q = 1) : d249564 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27275, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27276 q = 1) (hb : d152854 q = 1) : d249565 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27276, d249565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27276, d249565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d27282 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d27283 q = 1) (hb : d152855 q = 1) : d249566 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27283, d152855, d249566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27283, d152855, d249566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro62448 (p : Pattern) (ha : d27288 p = 1) (hb : d152855 p = 1) : d249575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27272 q = 1) (hb : d152854 q = 1) : d249561 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
  have h2 (q : Pattern) (ha : d27020 q = 1) (hb : d152854 q = 1) : d249406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
    | true =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27273 q = 1) (hb : d152854 q = 1) : d249562 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27273, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27021 q = 1) (hb : d152854 q = 1) : d249407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27274 q = 1) (hb : d152854 q = 1) : d249563 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27274, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27275 q = 1) (hb : d152854 q = 1) : d249564 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27275, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27278 q = 1) (hb : d152854 q = 1) : d249570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27278, d249570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27278, d249570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62428 q ha hb
  have h8 (q : Pattern) (ha : d27026 q = 1) (hb : d152854 q = 1) : d249413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27026, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62428 q ha hb
    | true =>
      simp only [d27026, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27279 q = 1) (hb : d152854 q = 1) : d249571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27279, d249571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27279, d249571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27027 q = 1) (hb : d152854 q = 1) : d249414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27027, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27027, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27280 q = 1) (hb : d152854 q = 1) : d249572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27280, d249572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27280, d249572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27281 q = 1) (hb : d152854 q = 1) : d249573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27281, d249573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27281, d249573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d27282 q = 1) (hb : d152854 q = 1) : d249574 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27282, d249574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27282, d249574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27287 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d27288 q = 1) (hb : d152855 q = 1) : d249575 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27288, d152855, d249575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d27288, d152855, d249575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62449 (p : Pattern) (ha : d27309 p = 1) (hb : d152855 p = 1) : d249587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27284 q = 1) (hb : d152855 q = 1) : d249567 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27284, d249567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62446 q ha hb
    | true =>
      simp only [d27284, d249567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62447 q ha hb
  have h2 (q : Pattern) (ha : d27285 q = 1) (hb : d152855 q = 1) : d249568 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27285, d249568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27285, d249568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27286 q = 1) (hb : d152855 q = 1) : d249569 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27286, d249569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27286, d249569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27289 q = 1) (hb : d152855 q = 1) : d249576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27289, d249576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62447 q ha hb
    | true =>
      simp only [d27289, d249576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62448 q ha hb
  have h5 (q : Pattern) (ha : d27290 q = 1) (hb : d152855 q = 1) : d249577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27290, d249577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27290, d249577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27291 q = 1) (hb : d152855 q = 1) : d249578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27291, d249578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27291, d249578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27292 q = 1) (hb : d152855 q = 1) : d249579 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27292, d249579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27292, d249579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27299 q = 1) (hb : d152855 q = 1) : d249576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27299, d249576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62447 q ha hb
    | true =>
      simp only [d27299, d249576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62418 q ha hb
  have h9 (q : Pattern) (ha : d27300 q = 1) (hb : d152855 q = 1) : d249577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27300, d249577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27300, d249577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27301 q = 1) (hb : d152855 q = 1) : d249578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27301, d249578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27301, d249578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27304 q = 1) (hb : d152855 q = 1) : d249582 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27304, d249582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62418 q ha hb
    | true =>
      simp only [d27304, d249582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62419 q ha hb
  have h12 (q : Pattern) (ha : d27305 q = 1) (hb : d152855 q = 1) : d249583 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27305, d249583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27305, d249583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27306 q = 1) (hb : d152855 q = 1) : d249584 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27306, d249584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27306, d249584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d27307 q = 1) (hb : d152855 q = 1) : d249585 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27307, d249585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27307, d249585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27308 q = 1) (hb : d152855 q = 1) : d249586 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27308, d249586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27308, d249586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d27309 q = 1) (hb : d152855 q = 1) : d249587 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27309, d249587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d27309, d249587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62450 (p : Pattern) (ha : d27314 p = 1) (hb : d152855 p = 1) : d249592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27299 q = 1) (hb : d152855 q = 1) : d249576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27299, d249576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62447 q ha hb
    | true =>
      simp only [d27299, d249576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62418 q ha hb
  have h2 (q : Pattern) (ha : d27300 q = 1) (hb : d152855 q = 1) : d249577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27300, d249577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27300, d249577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27301 q = 1) (hb : d152855 q = 1) : d249578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27301, d249578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27301, d249578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27304 q = 1) (hb : d152855 q = 1) : d249582 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27304, d249582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62418 q ha hb
    | true =>
      simp only [d27304, d249582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62419 q ha hb
  have h5 (q : Pattern) (ha : d27305 q = 1) (hb : d152855 q = 1) : d249583 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27305, d249583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27305, d249583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27306 q = 1) (hb : d152855 q = 1) : d249584 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27306, d249584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27306, d249584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27307 q = 1) (hb : d152855 q = 1) : d249585 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27307, d249585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27307, d249585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27312 q = 1) (hb : d152855 q = 1) : d249590 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27312, d249590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27312, d249590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27313 q = 1) (hb : d152855 q = 1) : d249591 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27313, d249591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27313, d249591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27314 q = 1) (hb : d152855 q = 1) : d249592 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27314, d249592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27314, d249592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62451 (p : Pattern) (ha : d27320 p = 1) (hb : d152855 p = 1) : d249598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27310 q = 1) (hb : d152855 q = 1) : d249588 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27310, d249588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62449 q ha hb
    | true =>
      simp only [d27310, d249588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27311 q = 1) (hb : d152855 q = 1) : d249589 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27311, d249589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27311, d249589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27315 q = 1) (hb : d152855 q = 1) : d249593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27315, d249593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62450 q ha hb
    | true =>
      simp only [d27315, d249593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27316 q = 1) (hb : d152855 q = 1) : d249594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27316, d249594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27316, d249594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27317 q = 1) (hb : d152855 q = 1) : d249595 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27317, d249595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27317, d249595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27318 q = 1) (hb : d152855 q = 1) : d249596 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27318, d249596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27318, d249596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27319 q = 1) (hb : d152855 q = 1) : d249597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27319, d249597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27319, d249597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27320 q = 1) (hb : d152855 q = 1) : d249598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27320, d249598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27320, d249598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62452 (p : Pattern) (ha : d27328 p = 1) (hb : d152855 p = 1) : d249606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27315 q = 1) (hb : d152855 q = 1) : d249593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27315, d249593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62450 q ha hb
    | true =>
      simp only [d27315, d249593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27316 q = 1) (hb : d152855 q = 1) : d249594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27316, d249594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27316, d249594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27323 q = 1) (hb : d152855 q = 1) : d249601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27323, d249601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62420 q ha hb
    | true =>
      simp only [d27323, d249601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27324 q = 1) (hb : d152855 q = 1) : d249602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27324, d249602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27324, d249602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27325 q = 1) (hb : d152855 q = 1) : d249603 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27325, d249603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27325, d249603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27326 q = 1) (hb : d152855 q = 1) : d249604 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27326, d249604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27326, d249604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27327 q = 1) (hb : d152855 q = 1) : d249605 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27327, d249605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27327, d249605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27328 q = 1) (hb : d152855 q = 1) : d249606 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27328, d249606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27328, d249606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62453 (p : Pattern) (ha : d27385 p = 1) (hb : d152855 p = 1) : d249575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27272 q = 1) (hb : d152854 q = 1) : d249561 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
  have h2 (q : Pattern) (ha : d27020 q = 1) (hb : d152854 q = 1) : d249406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62402 q ha hb
    | true =>
      simp only [d27020, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27273 q = 1) (hb : d152854 q = 1) : d249562 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27273, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27021 q = 1) (hb : d152854 q = 1) : d249407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27021, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27274 q = 1) (hb : d152854 q = 1) : d249563 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27274, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27275 q = 1) (hb : d152854 q = 1) : d249564 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27275, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27293 q = 1) (hb : d152854 q = 1) : d249570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27293, d249570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27293, d249570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62404 q ha hb
  have h8 (q : Pattern) (ha : d27036 q = 1) (hb : d152854 q = 1) : d249413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62404 q ha hb
    | true =>
      simp only [d27036, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27294 q = 1) (hb : d152854 q = 1) : d249571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27294, d249571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27294, d249571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27037 q = 1) (hb : d152854 q = 1) : d249414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27037, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27295 q = 1) (hb : d152854 q = 1) : d249572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27295, d249572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27295, d249572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27296 q = 1) (hb : d152854 q = 1) : d249573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27296, d249573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27296, d249573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d27297 q = 1) (hb : d152854 q = 1) : d249574 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27297, d249574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27297, d249574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27384 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d27385 q = 1) (hb : d152855 q = 1) : d249575 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27385, d152855, d249575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d27385, d152855, d249575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62454 (p : Pattern) (ha : d27391 p = 1) (hb : d152855 p = 1) : d157913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27386 q = 1) (hb : d152854 q = 1) : d157908 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27386, d157908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27386, d157908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62433 q ha hb
  have h2 (q : Pattern) (ha : d27192 q = 1) (hb : d152854 q = 1) : d157726 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27192, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62433 q ha hb
    | true =>
      simp only [d27192, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27387 q = 1) (hb : d152854 q = 1) : d157909 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27387, d157909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27387, d157909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27193 q = 1) (hb : d152854 q = 1) : d157727 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27193, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27193, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27388 q = 1) (hb : d152854 q = 1) : d157910 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27388, d157910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27388, d157910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27389 q = 1) (hb : d152854 q = 1) : d157911 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27389, d157911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27389, d157911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27390 q = 1) (hb : d152854 q = 1) : d157912 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27390, d157912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27390, d157912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d27391 q = 1) (hb : d152855 q = 1) : d157913 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27391, d152855, d157913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27391, d152855, d157913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62455 (p : Pattern) (ha : d27397 p = 1) (hb : d152855 p = 1) : d249614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27299 q = 1) (hb : d152855 q = 1) : d249576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27299, d249576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62447 q ha hb
    | true =>
      simp only [d27299, d249576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62418 q ha hb
  have h2 (q : Pattern) (ha : d27300 q = 1) (hb : d152855 q = 1) : d249577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27300, d249577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27300, d249577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27301 q = 1) (hb : d152855 q = 1) : d249578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27301, d249578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27301, d249578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27304 q = 1) (hb : d152855 q = 1) : d249582 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27304, d249582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62418 q ha hb
    | true =>
      simp only [d27304, d249582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62419 q ha hb
  have h5 (q : Pattern) (ha : d27305 q = 1) (hb : d152855 q = 1) : d249583 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27305, d249583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27305, d249583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27306 q = 1) (hb : d152855 q = 1) : d249584 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27306, d249584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27306, d249584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27307 q = 1) (hb : d152855 q = 1) : d249585 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27307, d249585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27307, d249585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27392 q = 1) (hb : d152855 q = 1) : d249609 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27392, d249609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62453 q ha hb
    | true =>
      simp only [d27392, d249609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62454 q ha hb
  have h9 (q : Pattern) (ha : d27393 q = 1) (hb : d152855 q = 1) : d249610 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27393, d249610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27393, d249610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27394 q = 1) (hb : d152855 q = 1) : d249611 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27394, d249611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27394, d249611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27395 q = 1) (hb : d152855 q = 1) : d249612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27395, d249612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27395, d249612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d27396 q = 1) (hb : d152855 q = 1) : d249613 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27396, d249613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27396, d249613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27397 q = 1) (hb : d152855 q = 1) : d249614 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27397, d249614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d27397, d249614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro62456 (p : Pattern) (ha : d27403 p = 1) (hb : d152855 p = 1) : d249620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27398 q = 1) (hb : d152855 q = 1) : d249615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27398, d249615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62455 q ha hb
    | true =>
      simp only [d27398, d249615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27399 q = 1) (hb : d152855 q = 1) : d249616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27399, d249616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27399, d249616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27400 q = 1) (hb : d152855 q = 1) : d249617 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27400, d249617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27400, d249617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27401 q = 1) (hb : d152855 q = 1) : d249618 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27401, d249618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27401, d249618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27402 q = 1) (hb : d152855 q = 1) : d249619 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27402, d249619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27402, d249619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27403 q = 1) (hb : d152855 q = 1) : d249620 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27403, d249620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27403, d249620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62457 (p : Pattern) (ha : d152855 p = 1) (hb : d202242 p = 1) : d249626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27329 q = 1) (hb : d152855 q = 1) : d249607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27329, d249607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62451 q ha hb
    | true =>
      simp only [d27329, d249607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62452 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202238 q = 1) : d249608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202238, d249608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202238, d249608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d27404 q = 1) (hb : d152855 q = 1) : d249621 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27404, d249621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62456 q ha hb
    | true =>
      simp only [d27404, d249621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27405 q = 1) (hb : d152855 q = 1) : d249622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27405, d249622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27405, d249622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202239 q = 1) : d249623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202239, d249623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202239, d249623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202240 q = 1) : d249624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202240, d249624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202240, d249624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202241 q = 1) : d249625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202241, d249625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202241, d249625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202242 q = 1) : d249626 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202242, d249626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202242, d249626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62458 (p : Pattern) (ha : d152855 p = 1) (hb : d202248 p = 1) : d249643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27075 q = 1) (hb : d152855 q = 1) : d249451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27075, d249451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27075, d249451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62411 q ha hb
  have h2 (q : Pattern) (ha : d27076 q = 1) (hb : d152855 q = 1) : d249452 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27076, d249452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27076, d249452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27085 q = 1) (hb : d152855 q = 1) : d249461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27085, d249461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62411 q ha hb
    | true =>
      simp only [d27085, d249461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62414 q ha hb
  have h4 (q : Pattern) (ha : d27086 q = 1) (hb : d152855 q = 1) : d249462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27086, d249462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27086, d249462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27087 q = 1) (hb : d152855 q = 1) : d249463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d27087, d249463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27087, d249463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202226 q = 1) : d249534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202226, d249534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62437 q ha hb
    | true =>
      simp only [d202226, d249534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62444 q ha hb
  have h7 (q : Pattern) (ha : d27253 q = 1) (hb : d152855 q = 1) : d249547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27253, d249547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62415 q ha hb
    | true =>
      simp only [d27253, d249547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62416 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202227 q = 1) : d249548 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202227, d249548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202227, d249548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202228 q = 1) : d249549 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202228, d249549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202228, d249549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d202229 q = 1) : d249550 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202229, d249550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d202229, d249550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d202233 q = 1) : d249554 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202233, d249554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202233, d249554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62445 q ha hb
  have h12 (q : Pattern) (ha : d27262 q = 1) (hb : d152855 q = 1) : d249556 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27262, d249556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27262, d249556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62417 q ha hb
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202234 q = 1) : d249557 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202234, d249557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202234, d249557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202235 q = 1) : d249558 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202235, d249558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202235, d249558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202236 q = 1) : d249559 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202236, d249559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202236, d249559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d152855 q = 1) (hb : d202237 q = 1) : d249560 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202237, d249560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202237, d249560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d152855 q = 1) (hb : d202243 q = 1) : d249627 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202243, d249627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202243, d249627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62457 q ha hb
  have h18 (q : Pattern) (ha : d27421 q = 1) (hb : d152855 q = 1) : d249638 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27421, d249638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27421, d249638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62422 q ha hb
  have h19 (q : Pattern) (ha : d152855 q = 1) (hb : d202244 q = 1) : d249639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202244, d249639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202244, d249639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d152855 q = 1) (hb : d202245 q = 1) : d249640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202245, d249640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202245, d249640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d152855 q = 1) (hb : d202246 q = 1) : d249641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202246, d249641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202246, d249641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d152855 q = 1) (hb : d202247 q = 1) : d249642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202247, d249642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202247, d249642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202248 q = 1) : d249643 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202248, d249643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202248, d249643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62459 (p : Pattern) (ha : d152855 p = 1) (hb : d202254 p = 1) : d249649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202249 q = 1) : d249644 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202249, d249644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202249, d249644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62458 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202250 q = 1) : d249645 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202250, d249645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202250, d249645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202251 q = 1) : d249646 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202251, d249646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202251, d249646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202252 q = 1) : d249647 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202252, d249647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202252, d249647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202253 q = 1) : d249648 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202253, d249648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202253, d249648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202254 q = 1) : d249649 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202254, d249649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202254, d249649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62460 (p : Pattern) (ha : d152855 p = 1) (hb : d202260 p = 1) : d249655 p = 1 := by
  have h0 (q : Pattern) (ha : d152855 q = 1) (hb : d202089 q = 1) : d248673 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202089, d248673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62185 q ha hb
    | true =>
      simp only [d202089, d248673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62230 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202129 q = 1) : d248853 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202129, d248853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202129, d248853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62282 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202130 q = 1) : d248854 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202130, d248854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202130, d248854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202170 q = 1) : d249121 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202170, d249121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202170, d249121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62341 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202171 q = 1) : d249122 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202171, d249122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202171, d249122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202172 q = 1) : d249123 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202172, d249123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202172, d249123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202212 q = 1) : d249401 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202212, d249401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202212, d249401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62401 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202213 q = 1) : d249402 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202213, d249402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202213, d249402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202214 q = 1) : d249403 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202214, d249403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202214, d249403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d202215 q = 1) : d249404 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d202215, d249404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202215, d249404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d202255 q = 1) : d249650 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202255, d249650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202255, d249650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62459 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202256 q = 1) : d249651 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202256, d249651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202256, d249651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202257 q = 1) : d249652 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202257, d249652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202257, d249652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202258 q = 1) : d249653 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d202258, d249653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202258, d249653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202259 q = 1) : d249654 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d202259, d249654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202259, d249654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d152855 q = 1) (hb : d202260 q = 1) : d249655 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d202260, d249655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202260, d249655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro62461 (p : Pattern) (ha : d152855 p = 1) (hb : d202266 p = 1) : d249661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202261 q = 1) : d249656 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d202261, d249656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62460 q ha hb
    | true =>
      simp only [d202261, d249656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202262 q = 1) : d249657 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d202262, d249657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202262, d249657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202263 q = 1) : d249658 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d202263, d249658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202263, d249658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202264 q = 1) : d249659 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d202264, d249659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202264, d249659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202265 q = 1) : d249660 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d202265, d249660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202265, d249660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202266 q = 1) : d249661 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d202266, d249661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202266, d249661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62462 (p : Pattern) (ha : d152855 p = 1) (hb : d202272 p = 1) : d249667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202267 q = 1) : d249662 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d202267, d249662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62461 q ha hb
    | true =>
      simp only [d202267, d249662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202268 q = 1) : d249663 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d202268, d249663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202268, d249663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202269 q = 1) : d249664 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d202269, d249664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202269, d249664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202270 q = 1) : d249665 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d202270, d249665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202270, d249665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202271 q = 1) : d249666 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d202271, d249666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202271, d249666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202272 q = 1) : d249667 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d202272, d249667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202272, d249667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62463 (p : Pattern) (ha : d152855 p = 1) (hb : d202278 p = 1) : d249673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202273 q = 1) : d249668 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d202273, d249668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62462 q ha hb
    | true =>
      simp only [d202273, d249668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202274 q = 1) : d249669 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d202274, d249669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202274, d249669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202275 q = 1) : d249670 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d202275, d249670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202275, d249670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202276 q = 1) : d249671 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d202276, d249671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202276, d249671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202277 q = 1) : d249672 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d202277, d249672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202277, d249672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202278 q = 1) : d249673 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d202278, d249673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202278, d249673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62464 (p : Pattern) (ha : d152855 p = 1) (hb : d202284 p = 1) : d249679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202279 q = 1) : d249674 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d202279, d249674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62463 q ha hb
    | true =>
      simp only [d202279, d249674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202280 q = 1) : d249675 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d202280, d249675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202280, d249675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202281 q = 1) : d249676 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d202281, d249676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202281, d249676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202282 q = 1) : d249677 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d202282, d249677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202282, d249677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202283 q = 1) : d249678 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d202283, d249678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202283, d249678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202284 q = 1) : d249679 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d202284, d249679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202284, d249679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62465 (p : Pattern) (ha : d152855 p = 1) (hb : d202290 p = 1) : d249685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202285 q = 1) : d249680 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d202285, d249680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62464 q ha hb
    | true =>
      simp only [d202285, d249680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202286 q = 1) : d249681 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d202286, d249681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202286, d249681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202287 q = 1) : d249682 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d202287, d249682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202287, d249682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202288 q = 1) : d249683 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d202288, d249683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202288, d249683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202289 q = 1) : d249684 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d202289, d249684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202289, d249684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202290 q = 1) : d249685 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d202290, d249685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202290, d249685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62466 (p : Pattern) (ha : d152855 p = 1) (hb : d202296 p = 1) : d249691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202291 q = 1) : d249686 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d202291, d249686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62465 q ha hb
    | true =>
      simp only [d202291, d249686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202292 q = 1) : d249687 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d202292, d249687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202292, d249687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202293 q = 1) : d249688 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d202293, d249688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202293, d249688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202294 q = 1) : d249689 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d202294, d249689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202294, d249689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202295 q = 1) : d249690 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d202295, d249690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202295, d249690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202296 q = 1) : d249691 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d202296, d249691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202296, d249691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62467 (p : Pattern) (ha : d152855 p = 1) (hb : d202302 p = 1) : d249697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202297 q = 1) : d249692 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d202297, d249692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62466 q ha hb
    | true =>
      simp only [d202297, d249692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202298 q = 1) : d249693 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d202298, d249693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202298, d249693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202299 q = 1) : d249694 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d202299, d249694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202299, d249694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202300 q = 1) : d249695 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d202300, d249695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202300, d249695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202301 q = 1) : d249696 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d202301, d249696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202301, d249696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202302 q = 1) : d249697 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d202302, d249697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202302, d249697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62468 (p : Pattern) (ha : d51875 p = 1) (hb : d156536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d22 q = 1) (hb : d51874 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d23 q = 1) (hb : d51875 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51875 q = 1) (hb : d156536 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62469 (p : Pattern) (ha : d118619 p = 1) (hb : d156542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118615 q = 1) (hb : d156537 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118615, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62468 q ha hb
    | true =>
      simp only [d118615, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118616 q = 1) (hb : d156538 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118616, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118616, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118617 q = 1) (hb : d156539 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118617, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118617, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118618 q = 1) (hb : d156540 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118618, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118618, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118619 q = 1) (hb : d156541 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118619, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118619, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118619 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d118619 q = 1) (hb : d156542 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62470 (p : Pattern) (ha : d118625 p = 1) (hb : d156548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118620 q = 1) (hb : d156543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118620, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62469 q ha hb
    | true =>
      simp only [d118620, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118621 q = 1) (hb : d156544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118621, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118621, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118622 q = 1) (hb : d156545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118622, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118622, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118623 q = 1) (hb : d156546 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118623, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118623, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118624 q = 1) (hb : d156547 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118624, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118624, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118625 q = 1) (hb : d156548 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118625, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118625, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62471 (p : Pattern) (ha : d118631 p = 1) (hb : d156554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118629 q = 1) (hb : d156552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118629, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118629, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118630 q = 1) (hb : d156553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118630, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118630, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118631 q = 1) (hb : d156554 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118631, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118631, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62472 (p : Pattern) (ha : d118637 p = 1) (hb : d156560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118632 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q ha hb
    | true =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118633 q = 1) (hb : d156556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118633, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118633, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118634 q = 1) (hb : d156557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118634, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118634, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118635 q = 1) (hb : d156558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118635, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118635, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118636 q = 1) (hb : d156559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118636, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118636, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118637 q = 1) (hb : d156560 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118637, d156560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118637, d156560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62473 (p : Pattern) (ha : d118638 p = 1) (hb : d156561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118629 q = 1) (hb : d156552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118629, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118629, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118630 q = 1) (hb : d156553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118630, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118630, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118638 q = 1) (hb : d156561 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118638, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118638, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62474 (p : Pattern) (ha : d118644 p = 1) (hb : d156567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118632 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q ha hb
    | true =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118633 q = 1) (hb : d156556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118633, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118633, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118634 q = 1) (hb : d156557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118634, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118634, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118635 q = 1) (hb : d156558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118635, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118635, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118636 q = 1) (hb : d156559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118636, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118636, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118639 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q ha hb
    | true =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118640 q = 1) (hb : d156563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118640, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118640, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118641 q = 1) (hb : d156564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118641, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118641, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118642 q = 1) (hb : d156565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118642, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118642, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118643 q = 1) (hb : d156566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118643, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118643, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118644 q = 1) (hb : d156567 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118644, d156567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118644, d156567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62475 (p : Pattern) (ha : d118649 p = 1) (hb : d156572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118639 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q ha hb
    | true =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118640 q = 1) (hb : d156563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118640, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118640, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118641 q = 1) (hb : d156564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118641, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118641, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118642 q = 1) (hb : d156565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118642, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118642, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118643 q = 1) (hb : d156566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118643, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118643, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118649 q = 1) (hb : d156572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118649, d156572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118649, d156572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62476 (p : Pattern) (ha : d118659 p = 1) (hb : d156583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118655 q = 1) (hb : d156578 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118655, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118655, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62468 q ha hb
  have h2 (q : Pattern) (ha : d118615 q = 1) (hb : d156537 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118615, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62468 q ha hb
    | true =>
      simp only [d118615, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118656 q = 1) (hb : d156579 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118656, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118656, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118616 q = 1) (hb : d156538 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118616, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118616, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118657 q = 1) (hb : d156580 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118657, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118657, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118658 q = 1) (hb : d156581 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118658, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118658, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118659 q = 1) (hb : d156582 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118659, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118659, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d118659 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d118659 q = 1) (hb : d156583 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62477 (p : Pattern) (ha : d118665 p = 1) (hb : d156589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118660 q = 1) (hb : d156584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118660, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62476 q ha hb
    | true =>
      simp only [d118660, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118661 q = 1) (hb : d156585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118661, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118661, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118662 q = 1) (hb : d156586 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118662, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118662, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118663 q = 1) (hb : d156587 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118663, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118663, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118664 q = 1) (hb : d156588 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118664, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118664, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118665 q = 1) (hb : d156589 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118665, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118665, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62478 (p : Pattern) (ha : d118671 p = 1) (hb : d156595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118666 q = 1) (hb : d156590 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118666, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62477 q ha hb
    | true =>
      simp only [d118666, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118667 q = 1) (hb : d156591 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118667, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118667, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118668 q = 1) (hb : d156592 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118668, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118668, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118669 q = 1) (hb : d156593 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118669, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118669, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118670 q = 1) (hb : d156594 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118670, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118670, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118671 q = 1) (hb : d156595 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118671, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118671, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62479 (p : Pattern) (ha : d118677 p = 1) (hb : d156601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118672 q = 1) (hb : d156596 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118672, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62478 q ha hb
    | true =>
      simp only [d118672, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118673 q = 1) (hb : d156597 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118673, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118673, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118674 q = 1) (hb : d156598 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118674, d156598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118674, d156598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118675 q = 1) (hb : d156599 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118675, d156599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118675, d156599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118676 q = 1) (hb : d156600 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118676, d156600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118676, d156600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118677 q = 1) (hb : d156601 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118677, d156601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118677, d156601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62480 (p : Pattern) (ha : d118683 p = 1) (hb : d156607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118645 q = 1) (hb : d156568 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118645, d156568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62472 q ha hb
    | true =>
      simp only [d118645, d156568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62474 q ha hb
  have h2 (q : Pattern) (ha : d118646 q = 1) (hb : d156569 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118646, d156569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118646, d156569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118647 q = 1) (hb : d156570 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118647, d156570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118647, d156570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118648 q = 1) (hb : d156571 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118648, d156571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118648, d156571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118650 q = 1) (hb : d156573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118650, d156573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118650, d156573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62475 q ha hb
  have h6 (q : Pattern) (ha : d118651 q = 1) (hb : d156574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118651, d156574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118651, d156574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118652 q = 1) (hb : d156575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118652, d156575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118652, d156575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d118653 q = 1) (hb : d156576 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118653, d156576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118653, d156576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118654 q = 1) (hb : d156577 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118654, d156577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118654, d156577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118678 q = 1) (hb : d156602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118678, d156602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118678, d156602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62479 q ha hb
  have h11 (q : Pattern) (ha : d118679 q = 1) (hb : d156603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118679, d156603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118679, d156603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d118680 q = 1) (hb : d156604 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118680, d156604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118680, d156604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d118681 q = 1) (hb : d156605 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118681, d156605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d118681, d156605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d118682 q = 1) (hb : d156606 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118682, d156606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d118682, d156606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d118683 q = 1) (hb : d156607 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d118683, d156607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d118683, d156607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62481 (p : Pattern) (ha : d118693 p = 1) (hb : d156617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118632 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q ha hb
    | true =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118689 q = 1) (hb : d156613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118689, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118689, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118690 q = 1) (hb : d156614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118690, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118690, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118691 q = 1) (hb : d156615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118691, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118691, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118692 q = 1) (hb : d156616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118692, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118692, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118693 q = 1) (hb : d156617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118693, d156617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118693, d156617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62482 (p : Pattern) (ha : d118700 p = 1) (hb : d156624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118632 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q ha hb
    | true =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118689 q = 1) (hb : d156613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118689, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118689, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118690 q = 1) (hb : d156614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118690, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118690, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118691 q = 1) (hb : d156615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118691, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118691, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118692 q = 1) (hb : d156616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118692, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118692, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118639 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q ha hb
    | true =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118696 q = 1) (hb : d156620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118696, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118696, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118697 q = 1) (hb : d156621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118697, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118697, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118698 q = 1) (hb : d156622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118698, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118698, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118699 q = 1) (hb : d156623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118699, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118699, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118700 q = 1) (hb : d156624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118700, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118700, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62483 (p : Pattern) (ha : d118756 p = 1) (hb : d156682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118632 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q ha hb
    | true =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118689 q = 1) (hb : d156613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118689, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118689, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118690 q = 1) (hb : d156614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118690, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118690, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118691 q = 1) (hb : d156615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118691, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118691, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118692 q = 1) (hb : d156616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118692, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118692, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118756 q = 1) (hb : d156682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118756, d156682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118756, d156682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62484 (p : Pattern) (ha : d118705 p = 1) (hb : d156629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118629 q = 1) (hb : d156552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118629, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118629, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118704 q = 1) (hb : d156628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118704, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118704, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118705 q = 1) (hb : d156629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118705, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118705, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62485 (p : Pattern) (ha : d118712 p = 1) (hb : d156636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118710 q = 1) (hb : d156634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118710, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118710, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118711 q = 1) (hb : d156635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118711, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118711, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118712 q = 1) (hb : d156636 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118712, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118712, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62486 (p : Pattern) (ha : d74175 p = 1) (hb : d156640 p = 1) : d249698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74175 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9796 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d21 q = 1) : d21 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d25102 q = 1) (hb : d74174 q = 1) : d29112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d74174, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25102, d74174, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d25103 q = 1) (hb : d74175 q = 1) : d29113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d74175, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25103, d74175, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d74175 q = 1) (hb : d156640 q = 1) : d249698 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d156640, d249698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156640, d249698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62487 (p : Pattern) (ha : d156646 p = 1) (hb : d247403 p = 1) : d249704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156641 q = 1) (hb : d247399 q = 1) : d249699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156641, d247399, d249699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62486 q hb ha
    | true =>
      simp only [d156641, d247399, d249699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156642 q = 1) (hb : d247400 q = 1) : d249700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156642, d247400, d249700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156642, d247400, d249700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d156643 q = 1) (hb : d247401 q = 1) : d249701 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156643, d247401, d249701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156643, d247401, d249701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156644 q = 1) (hb : d247402 q = 1) : d249702 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156644, d247402, d249702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156644, d247402, d249702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d118615 q = 1) (hb : d156537 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118615, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62468 q ha hb
    | true =>
      simp only [d118615, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118616 q = 1) (hb : d156538 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118616, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118616, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118617 q = 1) (hb : d156539 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118617, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118617, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118618 q = 1) (hb : d156540 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118618, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118618, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156645 q = 1) (hb : d247403 q = 1) : d249703 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156645, d247403, d249703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156645, d247403, d249703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d247403 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d156646 q = 1) (hb : d247403 q = 1) : d249704 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156646, d249704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156646, d249704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62488 (p : Pattern) (ha : d156652 p = 1) (hb : d247409 p = 1) : d249710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156647 q = 1) (hb : d247404 q = 1) : d249705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156647, d247404, d249705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62487 q ha hb
    | true =>
      simp only [d156647, d247404, d249705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62469 q hb ha
  have h2 (q : Pattern) (ha : d156648 q = 1) (hb : d247405 q = 1) : d249706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156648, d247405, d249706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156648, d247405, d249706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156649 q = 1) (hb : d247406 q = 1) : d249707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156649, d247406, d249707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156649, d247406, d249707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118620 q = 1) (hb : d156543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118620, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62469 q ha hb
    | true =>
      simp only [d118620, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118621 q = 1) (hb : d156544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118621, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118621, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118622 q = 1) (hb : d156545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118622, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118622, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156650 q = 1) (hb : d247407 q = 1) : d249708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156650, d247407, d249708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156650, d247407, d249708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d118623 q = 1) (hb : d156546 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118623, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118623, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156651 q = 1) (hb : d247408 q = 1) : d249709 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156651, d247408, d249709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156651, d247408, d249709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d156652 q = 1) (hb : d247409 q = 1) : d249710 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156652, d247409, d249710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156652, d247409, d249710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62489 (p : Pattern) (ha : d156658 p = 1) (hb : d247415 p = 1) : d249716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156653 q = 1) (hb : d247410 q = 1) : d249711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62488 q ha hb
    | true =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156654 q = 1) (hb : d247411 q = 1) : d249712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156655 q = 1) (hb : d247412 q = 1) : d249713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156656 q = 1) (hb : d247413 q = 1) : d249714 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156656, d247413, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156656, d247413, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156657 q = 1) (hb : d247414 q = 1) : d249715 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156657, d247414, d249715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156657, d247414, d249715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d156658 q = 1) (hb : d247415 q = 1) : d249716 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156658, d247415, d249716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156658, d247415, d249716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62490 (p : Pattern) (ha : d156664 p = 1) (hb : d247421 p = 1) : d249722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118706 q = 1) (hb : d156630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118706, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62484 q ha hb
    | true =>
      simp only [d118706, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118707 q = 1) (hb : d156631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118707, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118707, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118708 q = 1) (hb : d156632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118708, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118708, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118709 q = 1) (hb : d156633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118709, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118709, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118713 q = 1) (hb : d156637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118713, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62485 q ha hb
    | true =>
      simp only [d118713, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118714 q = 1) (hb : d156638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118714, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118714, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118715 q = 1) (hb : d156639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118715, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118715, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156659 q = 1) (hb : d247416 q = 1) : d249717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62489 q ha hb
    | true =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118632 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d156660 q = 1) (hb : d247417 q = 1) : d249718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156660, d247417, d249718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156660, d247417, d249718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118632 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q ha hb
    | true =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d118633 q = 1) (hb : d156556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118633, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118633, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156661 q = 1) (hb : d247418 q = 1) : d249719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156661, d247418, d249719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156661, d247418, d249719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d156662 q = 1) (hb : d247419 q = 1) : d249720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156662, d247419, d249720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d156662, d247419, d249720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156663 q = 1) (hb : d247420 q = 1) : d249721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156663, d247420, d249721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d156663, d247420, d249721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156664 q = 1) (hb : d247421 q = 1) : d249722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156664, d247421, d249722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156664, d247421, d249722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro62491 (p : Pattern) (ha : d118739 p = 1) (hb : d156665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118629 q = 1) (hb : d156552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118629, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118629, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118704 q = 1) (hb : d156628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118704, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118704, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118739 q = 1) (hb : d156665 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118739, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118739, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62492 (p : Pattern) (ha : d118744 p = 1) (hb : d156670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118628 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118628, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118710 q = 1) (hb : d156634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118710, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118710, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118711 q = 1) (hb : d156635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118711, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118711, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118744 q = 1) (hb : d156670 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118744, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118744, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62493 (p : Pattern) (ha : d156674 p = 1) (hb : d247422 p = 1) : d249723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156653 q = 1) (hb : d247410 q = 1) : d249711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62488 q ha hb
    | true =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156654 q = 1) (hb : d247411 q = 1) : d249712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156655 q = 1) (hb : d247412 q = 1) : d249713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156656 q = 1) (hb : d247413 q = 1) : d249714 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156656, d247413, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156656, d247413, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156657 q = 1) (hb : d247414 q = 1) : d249715 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156657, d247414, d249715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156657, d247414, d249715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d156674 q = 1) (hb : d247422 q = 1) : d249723 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156674, d247422, d249723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156674, d247422, d249723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62494 (p : Pattern) (ha : d156680 p = 1) (hb : d247428 p = 1) : d249729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118706 q = 1) (hb : d156630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118706, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62484 q ha hb
    | true =>
      simp only [d118706, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118707 q = 1) (hb : d156631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118707, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118707, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118708 q = 1) (hb : d156632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118708, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118708, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118709 q = 1) (hb : d156633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118709, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118709, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118713 q = 1) (hb : d156637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118713, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62485 q ha hb
    | true =>
      simp only [d118713, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118714 q = 1) (hb : d156638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118714, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118714, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118715 q = 1) (hb : d156639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118715, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118715, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156659 q = 1) (hb : d247416 q = 1) : d249717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62489 q ha hb
    | true =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118632 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d156660 q = 1) (hb : d247417 q = 1) : d249718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156660, d247417, d249718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156660, d247417, d249718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118632 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q ha hb
    | true =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d118633 q = 1) (hb : d156556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118633, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118633, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156661 q = 1) (hb : d247418 q = 1) : d249719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156661, d247418, d249719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156661, d247418, d249719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d156662 q = 1) (hb : d247419 q = 1) : d249720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156662, d247419, d249720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d156662, d247419, d249720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156663 q = 1) (hb : d247420 q = 1) : d249721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156663, d247420, d249721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d156663, d247420, d249721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d118740 q = 1) (hb : d156666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118740, d156666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62491 q ha hb
    | true =>
      simp only [d118740, d156666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d118741 q = 1) (hb : d156667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118741, d156667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118741, d156667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d118742 q = 1) (hb : d156668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118742, d156668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d118742, d156668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d118743 q = 1) (hb : d156669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118743, d156669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118743, d156669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d118745 q = 1) (hb : d156671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118745, d156671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62492 q ha hb
    | true =>
      simp only [d118745, d156671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d118746 q = 1) (hb : d156672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118746, d156672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118746, d156672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d118747 q = 1) (hb : d156673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118747, d156673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d118747, d156673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d156675 q = 1) (hb : d247423 q = 1) : d249724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156675, d247423, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62493 q ha hb
    | true =>
      simp only [d156675, d247423, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d118639 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d156676 q = 1) (hb : d247424 q = 1) : d249725 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156676, d247424, d249725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d156676, d247424, d249725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d118639 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q ha hb
    | true =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d118640 q = 1) (hb : d156563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118640, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d118640, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d156677 q = 1) (hb : d247425 q = 1) : d249726 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156677, d247425, d249726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d156677, d247425, d249726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d156678 q = 1) (hb : d247426 q = 1) : d249727 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156678, d247426, d249727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d156678, d247426, d249727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d156679 q = 1) (hb : d247427 q = 1) : d249728 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156679, d247427, d249728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d156679, d247427, d249728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d156680 q = 1) (hb : d247428 q = 1) : d249729 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156680, d247428, d249729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156680, d247428, d249729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro62495 (p : Pattern) (ha : d156689 p = 1) (hb : d247435 p = 1) : d249734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156675 q = 1) (hb : d247423 q = 1) : d249724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156675, d247423, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62493 q ha hb
    | true =>
      simp only [d156675, d247423, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156676 q = 1) (hb : d247424 q = 1) : d249725 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156676, d247424, d249725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156676, d247424, d249725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118639 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q ha hb
    | true =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118640 q = 1) (hb : d156563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118640, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118640, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156677 q = 1) (hb : d247425 q = 1) : d249726 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156677, d247425, d249726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156677, d247425, d249726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d156687 q = 1) (hb : d247433 q = 1) : d249727 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156687, d247433, d249727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156687, d247433, d249727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156688 q = 1) (hb : d247434 q = 1) : d249728 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156688, d247434, d249728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156688, d247434, d249728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156689 q = 1) (hb : d247435 q = 1) : d249734 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156689, d247435, d249734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156689, d247435, d249734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62496 (p : Pattern) (ha : d156700 p = 1) (hb : d247445 p = 1) : d249745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156695 q = 1) (hb : d247441 q = 1) : d249740 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156695, d247441, d249740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156695, d247441, d249740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62486 q hb ha
  have h2 (q : Pattern) (ha : d156641 q = 1) (hb : d247399 q = 1) : d249699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156641, d247399, d249699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62486 q hb ha
    | true =>
      simp only [d156641, d247399, d249699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d156696 q = 1) (hb : d247442 q = 1) : d249741 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156696, d247442, d249741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156696, d247442, d249741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156642 q = 1) (hb : d247400 q = 1) : d249700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156642, d247400, d249700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156642, d247400, d249700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d156697 q = 1) (hb : d247443 q = 1) : d249742 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156697, d247443, d249742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156697, d247443, d249742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156698 q = 1) (hb : d247444 q = 1) : d249743 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156698, d247444, d249743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156698, d247444, d249743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d118655 q = 1) (hb : d156578 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118655, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118655, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62468 q ha hb
  have h8 (q : Pattern) (ha : d118615 q = 1) (hb : d156537 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118615, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62468 q ha hb
    | true =>
      simp only [d118615, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118656 q = 1) (hb : d156579 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118656, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118656, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118616 q = 1) (hb : d156538 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118616, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118616, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d118657 q = 1) (hb : d156580 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118657, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d118657, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d118658 q = 1) (hb : d156581 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118658, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118658, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156699 q = 1) (hb : d247445 q = 1) : d249744 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156699, d247445, d249744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156699, d247445, d249744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247445 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156700 q = 1) (hb : d247445 q = 1) : d249745 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156700, d249745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156700, d249745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62497 (p : Pattern) (ha : d156706 p = 1) (hb : d247451 p = 1) : d249751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156701 q = 1) (hb : d247446 q = 1) : d249746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156701, d247446, d249746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62496 q ha hb
    | true =>
      simp only [d156701, d247446, d249746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62476 q hb ha
  have h2 (q : Pattern) (ha : d156702 q = 1) (hb : d247447 q = 1) : d249747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156702, d247447, d249747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156702, d247447, d249747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156703 q = 1) (hb : d247448 q = 1) : d249748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156703, d247448, d249748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156703, d247448, d249748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118660 q = 1) (hb : d156584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118660, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62476 q ha hb
    | true =>
      simp only [d118660, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118661 q = 1) (hb : d156585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118661, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118661, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118662 q = 1) (hb : d156586 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118662, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118662, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156704 q = 1) (hb : d247449 q = 1) : d249749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156704, d247449, d249749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156704, d247449, d249749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d118663 q = 1) (hb : d156587 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118663, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118663, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156705 q = 1) (hb : d247450 q = 1) : d249750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156705, d247450, d249750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156705, d247450, d249750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d156706 q = 1) (hb : d247451 q = 1) : d249751 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156706, d247451, d249751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156706, d247451, d249751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62498 (p : Pattern) (ha : d156712 p = 1) (hb : d247457 p = 1) : d249757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156707 q = 1) (hb : d247452 q = 1) : d249752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156707, d247452, d249752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62497 q ha hb
    | true =>
      simp only [d156707, d247452, d249752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156708 q = 1) (hb : d247453 q = 1) : d249753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156708, d247453, d249753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156708, d247453, d249753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118666 q = 1) (hb : d156590 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118666, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62477 q ha hb
    | true =>
      simp only [d118666, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118667 q = 1) (hb : d156591 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118667, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118667, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156709 q = 1) (hb : d247454 q = 1) : d249754 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156709, d247454, d249754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156709, d247454, d249754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156710 q = 1) (hb : d247455 q = 1) : d249755 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156710, d247455, d249755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156710, d247455, d249755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156711 q = 1) (hb : d247456 q = 1) : d249756 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156711, d247456, d249756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156711, d247456, d249756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d156712 q = 1) (hb : d247457 q = 1) : d249757 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156712, d247457, d249757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156712, d247457, d249757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62499 (p : Pattern) (ha : d156718 p = 1) (hb : d247463 p = 1) : d249763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156713 q = 1) (hb : d247458 q = 1) : d249758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156713, d247458, d249758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62498 q ha hb
    | true =>
      simp only [d156713, d247458, d249758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62478 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156714 q = 1) (hb : d247459 q = 1) : d249759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156714, d247459, d249759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156714, d247459, d249759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118672 q = 1) (hb : d156596 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118672, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62478 q ha hb
    | true =>
      simp only [d118672, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118673 q = 1) (hb : d156597 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118673, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118673, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156715 q = 1) (hb : d247460 q = 1) : d249760 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156715, d247460, d249760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156715, d247460, d249760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d156716 q = 1) (hb : d247461 q = 1) : d249761 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156716, d247461, d249761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156716, d247461, d249761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156717 q = 1) (hb : d247462 q = 1) : d249762 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156717, d247462, d249762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156717, d247462, d249762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156718 q = 1) (hb : d247463 q = 1) : d249763 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156718, d247463, d249763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156718, d247463, d249763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
end NetHack.Soko22Hazard87
