import NetHack.Soko22Hazard87.AndIntroBlocks0130
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro32750 (p : Pattern) (ha : d13323 p = 1) (hb : d112688 p = 1) : d114714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13307 q = 1) (hb : d112688 q = 1) : d13307 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13308 q = 1) (hb : d112688 q = 1) : d114700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32747 q ha hb
    | true =>
      simp only [d13308, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13309 q = 1) (hb : d112688 q = 1) : d114701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13310 q = 1) (hb : d112688 q = 1) : d114702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13310, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13311 q = 1) (hb : d112688 q = 1) : d114703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13312 q = 1) (hb : d112688 q = 1) : d114704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13317 q = 1) (hb : d112688 q = 1) : d13317 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13318 q = 1) (hb : d112688 q = 1) : d114709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32749 q ha hb
    | true =>
      simp only [d13318, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13319 q = 1) (hb : d112688 q = 1) : d114710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13320 q = 1) (hb : d112688 q = 1) : d114711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13320, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13321 q = 1) (hb : d112688 q = 1) : d114712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13322 q = 1) (hb : d112688 q = 1) : d114713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13323 q = 1) (hb : d112688 q = 1) : d114714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13323, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13323, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro32751 (p : Pattern) (ha : d13366 p = 1) (hb : d112688 p = 1) : d114693 p = 1 := by
  have h0 (q : Pattern) (ha : d13285 q = 1) (hb : d94753 q = 1) : d13285 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5120 q = 1) (hb : d94753 q = 1) : d5120 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5139 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5140 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5140, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d5141 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5141, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5142 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5142, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13286 q = 1) (hb : d112687 q = 1) : d114691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d112687, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13286, d112687, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d5143 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13365 q = 1) (hb : d112688 q = 1) : d114692 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13365, d112688, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13365, d112688, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13366 q = 1) (hb : d112688 q = 1) : d114693 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13366, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13366, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32752 (p : Pattern) (ha : d13376 p = 1) (hb : d112688 p = 1) : d114699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32751 q ha hb
    | true =>
      simp only [d13367, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13373 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13374 q = 1) (hb : d112688 q = 1) : d114697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13374, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13375 q = 1) (hb : d112688 q = 1) : d114698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13375, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13376 q = 1) (hb : d112688 q = 1) : d114699 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13376, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13376, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32753 (p : Pattern) (ha : d13460 p = 1) (hb : d112688 p = 1) : d114774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13307 q = 1) (hb : d112688 q = 1) : d13307 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13450 q = 1) (hb : d112688 q = 1) : d114700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13450, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32752 q ha hb
    | true =>
      simp only [d13450, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13451 q = 1) (hb : d112688 q = 1) : d114701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13451, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13451, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13452 q = 1) (hb : d112688 q = 1) : d114702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13452, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13452, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13453 q = 1) (hb : d112688 q = 1) : d114703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13453, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13453, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13454 q = 1) (hb : d112688 q = 1) : d114704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13454, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13454, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13459 q = 1) (hb : d112688 q = 1) : d13459 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13460 q = 1) (hb : d112688 q = 1) : d114774 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13460, d114774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13460, d114774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32754 (p : Pattern) (ha : d13328 p = 1) (hb : d112688 p = 1) : d114719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32746 q ha hb
    | true =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13301 q = 1) (hb : d112688 q = 1) : d114697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13301, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13327 q = 1) (hb : d112688 q = 1) : d114718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13328 q = 1) (hb : d112688 q = 1) : d114719 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13328, d114719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13328, d114719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32755 (p : Pattern) (ha : d13337 p = 1) (hb : d112688 p = 1) : d114726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32746 q ha hb
    | true =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13335 q = 1) (hb : d112688 q = 1) : d114724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13336 q = 1) (hb : d112688 q = 1) : d114725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13336, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13337 q = 1) (hb : d112688 q = 1) : d114726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13337, d114726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13337, d114726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32756 (p : Pattern) (ha : d13362 p = 1) (hb : d112688 p = 1) : d114735 p = 1 := by
  have h0 (q : Pattern) (ha : d13347 q = 1) (hb : d94753 q = 1) : d13347 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13282 q = 1) (hb : d94753 q = 1) : d13282 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13356 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13357 q = 1) (hb : d112686 q = 1) : d114730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13357, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13357, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d13358 q = 1) (hb : d112686 q = 1) : d114731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13358, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13358, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13359 q = 1) (hb : d112686 q = 1) : d114732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13359, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13359, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13360 q = 1) (hb : d112687 q = 1) : d114733 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13360, d112687, d114733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13360, d112687, d114733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13286 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13361 q = 1) (hb : d112688 q = 1) : d114734 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13361, d112688, d114734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13361, d112688, d114734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13362 q = 1) (hb : d112688 q = 1) : d114735 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13362, d114735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13362, d114735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32757 (p : Pattern) (ha : d13372 p = 1) (hb : d112688 p = 1) : d114741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d112688 q = 1) : d114736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32756 q ha hb
    | true =>
      simp only [d13363, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d112688 q = 1) : d114737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32751 q ha hb
    | true =>
      simp only [d13367, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d112688 q = 1) : d114738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d112688 q = 1) : d114739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d112688 q = 1) : d114740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13372 q = 1) (hb : d112688 q = 1) : d114741 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13372, d114741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13372, d114741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32758 (p : Pattern) (ha : d13417 p = 1) (hb : d112688 p = 1) : d114747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32746 q ha hb
    | true =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d112688 q = 1) : d114744 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d112688 q = 1) : d114745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d112688 q = 1) : d114746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13417 q = 1) (hb : d112688 q = 1) : d114747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13417, d114747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13417, d114747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32759 (p : Pattern) (ha : d112688 p = 1) (hb : d115442 p = 1) : d114753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13330 q = 1) (hb : d112688 q = 1) : d13330 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13331 q = 1) (hb : d112688 q = 1) : d114720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32754 q ha hb
    | true =>
      simp only [d13331, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13332 q = 1) (hb : d112688 q = 1) : d114721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13333 q = 1) (hb : d112688 q = 1) : d114722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13333, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13334 q = 1) (hb : d112688 q = 1) : d114723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d112688 q = 1) : d13340 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13341 q = 1) (hb : d112688 q = 1) : d114727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32755 q ha hb
    | true =>
      simp only [d13341, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13342 q = 1) (hb : d112688 q = 1) : d114728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13343 q = 1) (hb : d112688 q = 1) : d114729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13343, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13377 q = 1) (hb : d112688 q = 1) : d114742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32757 q ha hb
    | true =>
      simp only [d13377, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32752 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115438 q = 1) : d114743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115438, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d13418 q = 1) (hb : d112688 q = 1) : d114748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32758 q ha hb
    | true =>
      simp only [d13418, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13419 q = 1) (hb : d112688 q = 1) : d114749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13419, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115439 q = 1) : d114750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115439, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115440 q = 1) : d114751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115440, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115441 q = 1) : d114752 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115441, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115442 q = 1) : d114753 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d114753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115442, d114753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro32760 (p : Pattern) (ha : d13424 p = 1) (hb : d112688 p = 1) : d114754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32746 q ha hb
    | true =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13301 q = 1) (hb : d112688 q = 1) : d114697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13301, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13327 q = 1) (hb : d112688 q = 1) : d114718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13424 q = 1) (hb : d112688 q = 1) : d114754 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13424, d114754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13424, d114754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32761 (p : Pattern) (ha : d13430 p = 1) (hb : d112688 p = 1) : d114759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32746 q ha hb
    | true =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13335 q = 1) (hb : d112688 q = 1) : d114724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13336 q = 1) (hb : d112688 q = 1) : d114725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13336, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13430 q = 1) (hb : d112688 q = 1) : d114759 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13430, d114759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13430, d114759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32762 (p : Pattern) (ha : d13435 p = 1) (hb : d112688 p = 1) : d114763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d112688 q = 1) : d114736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32756 q ha hb
    | true =>
      simp only [d13363, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d112688 q = 1) : d114737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32751 q ha hb
    | true =>
      simp only [d13367, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d112688 q = 1) : d114738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d112688 q = 1) : d114739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d112688 q = 1) : d114740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13435 q = 1) (hb : d112688 q = 1) : d114763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13435, d114763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13435, d114763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32763 (p : Pattern) (ha : d13436 p = 1) (hb : d112688 p = 1) : d114708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32751 q ha hb
    | true =>
      simp only [d13367, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13373 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13374 q = 1) (hb : d112688 q = 1) : d114697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13374, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13375 q = 1) (hb : d112688 q = 1) : d114698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13375, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13436 q = 1) (hb : d112688 q = 1) : d114708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13436, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13436, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32764 (p : Pattern) (ha : d13442 p = 1) (hb : d112688 p = 1) : d114766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32746 q ha hb
    | true =>
      simp only [d13294, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d112688 q = 1) : d114744 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d112688 q = 1) : d114745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d112688 q = 1) : d114746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13442 q = 1) (hb : d112688 q = 1) : d114766 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13442, d114766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13442, d114766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32765 (p : Pattern) (ha : d112688 p = 1) (hb : d115447 p = 1) : d114772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13330 q = 1) (hb : d112688 q = 1) : d13330 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13331 q = 1) (hb : d112688 q = 1) : d114720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32754 q ha hb
    | true =>
      simp only [d13331, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13332 q = 1) (hb : d112688 q = 1) : d114721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13333 q = 1) (hb : d112688 q = 1) : d114722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13333, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13334 q = 1) (hb : d112688 q = 1) : d114723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d112688 q = 1) : d13340 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13341 q = 1) (hb : d112688 q = 1) : d114727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32755 q ha hb
    | true =>
      simp only [d13341, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13342 q = 1) (hb : d112688 q = 1) : d114728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13343 q = 1) (hb : d112688 q = 1) : d114729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13343, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13377 q = 1) (hb : d112688 q = 1) : d114742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32757 q ha hb
    | true =>
      simp only [d13377, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32752 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115438 q = 1) : d114743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115438, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d13418 q = 1) (hb : d112688 q = 1) : d114748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32758 q ha hb
    | true =>
      simp only [d13418, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13419 q = 1) (hb : d112688 q = 1) : d114749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13419, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115439 q = 1) : d114750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115439, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115440 q = 1) : d114751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115440, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115441 q = 1) : d114752 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115441, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13425 q = 1) (hb : d112688 q = 1) : d13425 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d13426 q = 1) (hb : d112688 q = 1) : d114755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13426, d114755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32760 q ha hb
    | true =>
      simp only [d13426, d114755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13427 q = 1) (hb : d112688 q = 1) : d114756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13427, d114756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13427, d114756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d13428 q = 1) (hb : d112688 q = 1) : d114757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13428, d114757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d13428, d114757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d13429 q = 1) (hb : d112688 q = 1) : d114758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13429, d114758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13429, d114758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13431 q = 1) (hb : d112688 q = 1) : d13431 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d13432 q = 1) (hb : d112688 q = 1) : d114760 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13432, d114760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32761 q ha hb
    | true =>
      simp only [d13432, d114760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d13433 q = 1) (hb : d112688 q = 1) : d114761 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13433, d114761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13433, d114761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d13434 q = 1) (hb : d112688 q = 1) : d114762 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13434, d114762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13434, d114762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d13437 q = 1) (hb : d112688 q = 1) : d114764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32762 q ha hb
    | true =>
      simp only [d13437, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32763 q ha hb
  have h27 (q : Pattern) (ha : d112688 q = 1) (hb : d115443 q = 1) : d114765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d115443, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d13443 q = 1) (hb : d112688 q = 1) : d114767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32764 q ha hb
    | true =>
      simp only [d13443, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d13444 q = 1) (hb : d112688 q = 1) : d114768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d13444, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d112688 q = 1) (hb : d115444 q = 1) : d114769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115444, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d112688 q = 1) (hb : d115445 q = 1) : d114770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115445, d114770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d115445, d114770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d112688 q = 1) (hb : d115446 q = 1) : d114771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115446, d114771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115446, d114771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d112688 q = 1) (hb : d115447 q = 1) : d114772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115447, d114772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115447, d114772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro32766 (p : Pattern) (ha : d112688 p = 1) (hb : d115454 p = 1) : d114781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13437 q = 1) (hb : d112688 q = 1) : d114764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32762 q ha hb
    | true =>
      simp only [d13437, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32763 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115443 q = 1) : d114765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115443, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13443 q = 1) (hb : d112688 q = 1) : d114767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32764 q ha hb
    | true =>
      simp only [d13443, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13444 q = 1) (hb : d112688 q = 1) : d114768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13444, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115444 q = 1) : d114769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115444, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115452 q = 1) : d114779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115452, d114779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115452, d114779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115453 q = 1) : d114780 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115453, d114780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115453, d114780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115454 q = 1) : d114781 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115454, d114781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115454, d114781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32767 (p : Pattern) (ha : d13505 p = 1) (hb : d112688 p = 1) : d114792 p = 1 := by
  have h0 (q : Pattern) (ha : d13485 q = 1) (hb : d94753 q = 1) : d13485 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13482 q = 1) (hb : d94753 q = 1) : d13482 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13495 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13496 q = 1) (hb : d112686 q = 1) : d114787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13496, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13496, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d13497 q = 1) (hb : d112686 q = 1) : d114788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13497, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13497, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13498 q = 1) (hb : d112686 q = 1) : d114789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13498, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13498, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13499 q = 1) (hb : d112687 q = 1) : d114790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13499, d112687, d114790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13499, d112687, d114790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13503 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13504 q = 1) (hb : d112688 q = 1) : d114791 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13504, d112688, d114791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13504, d112688, d114791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13505 q = 1) (hb : d112688 q = 1) : d114792 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13505, d114792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13505, d114792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32768 (p : Pattern) (ha : d13509 p = 1) (hb : d112688 p = 1) : d114797 p = 1 := by
  have h0 (q : Pattern) (ha : d13502 q = 1) (hb : d94753 q = 1) : d13502 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6495 q = 1) (hb : d94753 q = 1) : d6495 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6501 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6502 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6502, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6503 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6503, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6504 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6504, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13503 q = 1) (hb : d112687 q = 1) : d114795 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d112687, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13503, d112687, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d6505 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13508 q = 1) (hb : d112688 q = 1) : d114796 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13508, d112688, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13508, d112688, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13509 q = 1) (hb : d112688 q = 1) : d114797 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13509, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13509, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32769 (p : Pattern) (ha : d13515 p = 1) (hb : d112688 p = 1) : d114803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13506 q = 1) (hb : d112688 q = 1) : d114793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13506, d114793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32767 q ha hb
    | true =>
      simp only [d13506, d114793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13507 q = 1) (hb : d112688 q = 1) : d114794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13507, d114794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13507, d114794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13510 q = 1) (hb : d112688 q = 1) : d114798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32768 q ha hb
    | true =>
      simp only [d13510, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13511 q = 1) (hb : d112688 q = 1) : d114799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13512 q = 1) (hb : d112688 q = 1) : d114800 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13512, d114800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13512, d114800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13513 q = 1) (hb : d112688 q = 1) : d114801 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13513, d114801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13513, d114801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13514 q = 1) (hb : d112688 q = 1) : d114802 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13514, d114802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13514, d114802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13515 q = 1) (hb : d112688 q = 1) : d114803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13515, d114803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13515, d114803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32770 (p : Pattern) (ha : d13528 p = 1) (hb : d112688 p = 1) : d114807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13510 q = 1) (hb : d112688 q = 1) : d114798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32768 q ha hb
    | true =>
      simp only [d13510, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13511 q = 1) (hb : d112688 q = 1) : d114799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13524 q = 1) (hb : d112688 q = 1) : d13524 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13525 q = 1) (hb : d112688 q = 1) : d114804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13525, d114804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13525, d114804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13526 q = 1) (hb : d112688 q = 1) : d114805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13526, d114805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13526, d114805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13527 q = 1) (hb : d112688 q = 1) : d114806 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13527, d114806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13527, d114806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13528 q = 1) (hb : d112688 q = 1) : d114807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13528, d114807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13528, d114807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32771 (p : Pattern) (ha : d13569 p = 1) (hb : d112688 p = 1) : d114797 p = 1 := by
  have h0 (q : Pattern) (ha : d13502 q = 1) (hb : d94753 q = 1) : d13502 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6495 q = 1) (hb : d94753 q = 1) : d6495 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6501 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6502 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6502, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6503 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6503, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6504 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6504, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13503 q = 1) (hb : d112687 q = 1) : d114795 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d112687, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13503, d112687, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13520 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13568 q = 1) (hb : d112688 q = 1) : d114796 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13568, d112688, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13568, d112688, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13569 q = 1) (hb : d112688 q = 1) : d114797 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13569, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13569, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32772 (p : Pattern) (ha : d13575 p = 1) (hb : d112688 p = 1) : d114813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d112688 q = 1) : d114798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32771 q ha hb
    | true =>
      simp only [d13570, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d112688 q = 1) : d114799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13572 q = 1) (hb : d112688 q = 1) : d114810 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13572, d114810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13572, d114810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13573 q = 1) (hb : d112688 q = 1) : d114811 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13573, d114811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13573, d114811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13574 q = 1) (hb : d112688 q = 1) : d114812 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13574, d114812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13574, d114812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13575 q = 1) (hb : d112688 q = 1) : d114813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13575, d114813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13575, d114813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32773 (p : Pattern) (ha : d112688 p = 1) (hb : d115464 p = 1) : d114819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13529 q = 1) (hb : d112688 q = 1) : d114808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13529, d114808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32769 q ha hb
    | true =>
      simp only [d13529, d114808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32770 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115460 q = 1) : d114809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115460, d114809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115460, d114809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13576 q = 1) (hb : d112688 q = 1) : d114814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13576, d114814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32772 q ha hb
    | true =>
      simp only [d13576, d114814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13577 q = 1) (hb : d112688 q = 1) : d114815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13577, d114815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13577, d114815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115461 q = 1) : d114816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115461, d114816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115461, d114816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115462 q = 1) : d114817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115462, d114817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115462, d114817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115463 q = 1) : d114818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115463, d114818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115463, d114818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115464 q = 1) : d114819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115464, d114819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115464, d114819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32774 (p : Pattern) (ha : d112688 p = 1) (hb : d115470 p = 1) : d114825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13314 q = 1) (hb : d112688 q = 1) : d114706 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13314, d114706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13314, d114706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32748 q ha hb
  have h2 (q : Pattern) (ha : d13315 q = 1) (hb : d112688 q = 1) : d114707 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13315, d114707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13315, d114707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13324 q = 1) (hb : d112688 q = 1) : d114715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32748 q ha hb
    | true =>
      simp only [d13324, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32750 q ha hb
  have h4 (q : Pattern) (ha : d13325 q = 1) (hb : d112688 q = 1) : d114716 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13325, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13326 q = 1) (hb : d112688 q = 1) : d114717 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13326, d114717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13326, d114717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115448 q = 1) : d114773 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115448, d114773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32759 q ha hb
    | true =>
      simp only [d115448, d114773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32765 q ha hb
  have h7 (q : Pattern) (ha : d13466 q = 1) (hb : d112688 q = 1) : d13466 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13467 q = 1) (hb : d112688 q = 1) : d114775 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13467, d114775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32753 q ha hb
    | true =>
      simp only [d13467, d114775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115449 q = 1) : d114776 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115449, d114776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115449, d114776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d115450 q = 1) : d114777 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115450, d114777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115450, d114777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115451 q = 1) : d114778 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115451, d114778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115451, d114778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d115455 q = 1) : d114782 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115455, d114782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115455, d114782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32766 q ha hb
  have h13 (q : Pattern) (ha : d13476 q = 1) (hb : d112688 q = 1) : d13476 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115456 q = 1) : d114783 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115456, d114783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115456, d114783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115457 q = 1) : d114784 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115457, d114784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115457, d114784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115458 q = 1) : d114785 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115458, d114785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115458, d114785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115459 q = 1) : d114786 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115459, d114786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115459, d114786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112688 q = 1) (hb : d115465 q = 1) : d114820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115465, d114820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115465, d114820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32773 q ha hb
  have h19 (q : Pattern) (ha : d13593 q = 1) (hb : d112688 q = 1) : d13593 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d112688 q = 1) (hb : d115466 q = 1) : d114821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115466, d114821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115466, d114821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d112688 q = 1) (hb : d115467 q = 1) : d114822 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115467, d114822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115467, d114822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d112688 q = 1) (hb : d115468 q = 1) : d114823 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115468, d114823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115468, d114823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112688 q = 1) (hb : d115469 q = 1) : d114824 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115469, d114824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115469, d114824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d112688 q = 1) (hb : d115470 q = 1) : d114825 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115470, d114825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115470, d114825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro32775 (p : Pattern) (ha : d112688 p = 1) (hb : d115476 p = 1) : d114831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115471 q = 1) : d114826 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115471, d114826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115471, d114826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32774 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115472 q = 1) : d114827 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115472, d114827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115472, d114827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115473 q = 1) : d114828 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115473, d114828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115473, d114828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115474 q = 1) : d114829 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115474, d114829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115474, d114829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115475 q = 1) : d114830 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115475, d114830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115475, d114830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115476 q = 1) : d114831 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115476, d114831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115476, d114831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32776 (p : Pattern) (ha : d13620 p = 1) (hb : d112688 p = 1) : d114838 p = 1 := by
  have h0 (q : Pattern) (ha : d13612 q = 1) (hb : d94753 q = 1) : d13612 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5237 q = 1) (hb : d94753 q = 1) : d5237 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5252 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5253 q = 1) (hb : d112686 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5253, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d5254 q = 1) (hb : d112686 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5254, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5255 q = 1) (hb : d112686 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5255, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13613 q = 1) (hb : d112687 q = 1) : d114836 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d112687, d114836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13613, d112687, d114836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13618 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13619 q = 1) (hb : d112688 q = 1) : d114837 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13619, d112688, d114837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13619, d112688, d114837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13620 q = 1) (hb : d112688 q = 1) : d114838 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13620, d114838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13620, d114838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32777 (p : Pattern) (ha : d13630 p = 1) (hb : d112688 p = 1) : d114844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32776 q ha hb
    | true =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13628 q = 1) (hb : d112688 q = 1) : d114842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13628, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13629 q = 1) (hb : d112688 q = 1) : d114843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13629, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13630 q = 1) (hb : d112688 q = 1) : d114844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13630, d114844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13630, d114844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32778 (p : Pattern) (ha : d13640 p = 1) (hb : d112688 p = 1) : d114850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13634 q = 1) (hb : d112688 q = 1) : d13634 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13635 q = 1) (hb : d112688 q = 1) : d114845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32777 q ha hb
    | true =>
      simp only [d13635, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13636 q = 1) (hb : d112688 q = 1) : d114846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13637 q = 1) (hb : d112688 q = 1) : d114847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13637, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13638 q = 1) (hb : d112688 q = 1) : d114848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13639 q = 1) (hb : d112688 q = 1) : d114849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13640 q = 1) (hb : d112688 q = 1) : d114850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13640, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13640, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32779 (p : Pattern) (ha : d13643 p = 1) (hb : d112688 p = 1) : d114853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32776 q ha hb
    | true =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13628 q = 1) (hb : d112688 q = 1) : d114842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13628, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13629 q = 1) (hb : d112688 q = 1) : d114843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13629, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13643 q = 1) (hb : d112688 q = 1) : d114853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13643, d114853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13643, d114853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32780 (p : Pattern) (ha : d13650 p = 1) (hb : d112688 p = 1) : d114859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13634 q = 1) (hb : d112688 q = 1) : d13634 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13635 q = 1) (hb : d112688 q = 1) : d114845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32777 q ha hb
    | true =>
      simp only [d13635, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13636 q = 1) (hb : d112688 q = 1) : d114846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13637 q = 1) (hb : d112688 q = 1) : d114847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13637, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13638 q = 1) (hb : d112688 q = 1) : d114848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13639 q = 1) (hb : d112688 q = 1) : d114849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13644 q = 1) (hb : d112688 q = 1) : d13644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13645 q = 1) (hb : d112688 q = 1) : d114854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32779 q ha hb
    | true =>
      simp only [d13645, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13646 q = 1) (hb : d112688 q = 1) : d114855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13647 q = 1) (hb : d112688 q = 1) : d114856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13647, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13648 q = 1) (hb : d112688 q = 1) : d114857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13649 q = 1) (hb : d112688 q = 1) : d114858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13650 q = 1) (hb : d112688 q = 1) : d114859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13650, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13650, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro32781 (p : Pattern) (ha : d13693 p = 1) (hb : d112688 p = 1) : d114838 p = 1 := by
  have h0 (q : Pattern) (ha : d13612 q = 1) (hb : d94753 q = 1) : d13612 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5237 q = 1) (hb : d94753 q = 1) : d5237 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5252 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5253 q = 1) (hb : d112686 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5253, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d5254 q = 1) (hb : d112686 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5254, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5255 q = 1) (hb : d112686 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5255, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13613 q = 1) (hb : d112687 q = 1) : d114836 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d112687, d114836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13613, d112687, d114836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d5256 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13692 q = 1) (hb : d112688 q = 1) : d114837 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13692, d112688, d114837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13692, d112688, d114837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13693 q = 1) (hb : d112688 q = 1) : d114838 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13693, d114838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13693, d114838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32782 (p : Pattern) (ha : d13703 p = 1) (hb : d112688 p = 1) : d114844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32781 q ha hb
    | true =>
      simp only [d13694, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13700 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13701 q = 1) (hb : d112688 q = 1) : d114842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13701, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13702 q = 1) (hb : d112688 q = 1) : d114843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13702, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13703 q = 1) (hb : d112688 q = 1) : d114844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13703, d114844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13703, d114844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32783 (p : Pattern) (ha : d13787 p = 1) (hb : d112688 p = 1) : d114919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13634 q = 1) (hb : d112688 q = 1) : d13634 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13777 q = 1) (hb : d112688 q = 1) : d114845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13777, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32782 q ha hb
    | true =>
      simp only [d13777, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13778 q = 1) (hb : d112688 q = 1) : d114846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13778, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13778, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13779 q = 1) (hb : d112688 q = 1) : d114847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13779, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13779, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13780 q = 1) (hb : d112688 q = 1) : d114848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13780, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13780, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13781 q = 1) (hb : d112688 q = 1) : d114849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13781, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13781, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13786 q = 1) (hb : d112688 q = 1) : d13786 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13787 q = 1) (hb : d112688 q = 1) : d114919 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13787, d114919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13787, d114919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32784 (p : Pattern) (ha : d13655 p = 1) (hb : d112688 p = 1) : d114864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32776 q ha hb
    | true =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13628 q = 1) (hb : d112688 q = 1) : d114842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13628, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13654 q = 1) (hb : d112688 q = 1) : d114863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13655 q = 1) (hb : d112688 q = 1) : d114864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13655, d114864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13655, d114864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32785 (p : Pattern) (ha : d13664 p = 1) (hb : d112688 p = 1) : d114871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32776 q ha hb
    | true =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13662 q = 1) (hb : d112688 q = 1) : d114869 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13663 q = 1) (hb : d112688 q = 1) : d114870 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13663, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13664 q = 1) (hb : d112688 q = 1) : d114871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13664, d114871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13664, d114871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32786 (p : Pattern) (ha : d13689 p = 1) (hb : d112688 p = 1) : d114880 p = 1 := by
  have h0 (q : Pattern) (ha : d13674 q = 1) (hb : d94753 q = 1) : d13674 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13609 q = 1) (hb : d94753 q = 1) : d13609 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13683 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13684 q = 1) (hb : d112686 q = 1) : d114875 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13684, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13684, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d13685 q = 1) (hb : d112686 q = 1) : d114876 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13685, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13685, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13686 q = 1) (hb : d112686 q = 1) : d114877 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13686, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13686, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13687 q = 1) (hb : d112687 q = 1) : d114878 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13687, d112687, d114878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13687, d112687, d114878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13613 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13688 q = 1) (hb : d112688 q = 1) : d114879 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13688, d112688, d114879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13688, d112688, d114879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13689 q = 1) (hb : d112688 q = 1) : d114880 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13689, d114880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13689, d114880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32787 (p : Pattern) (ha : d13699 p = 1) (hb : d112688 p = 1) : d114886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d112688 q = 1) : d114881 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32786 q ha hb
    | true =>
      simp only [d13690, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d112688 q = 1) : d114882 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32781 q ha hb
    | true =>
      simp only [d13694, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d112688 q = 1) : d114883 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d112688 q = 1) : d114884 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d112688 q = 1) : d114885 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13699 q = 1) (hb : d112688 q = 1) : d114886 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13699, d114886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13699, d114886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32788 (p : Pattern) (ha : d13744 p = 1) (hb : d112688 p = 1) : d114892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32776 q ha hb
    | true =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d112688 q = 1) : d114889 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d112688 q = 1) : d114890 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d112688 q = 1) : d114891 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13744 q = 1) (hb : d112688 q = 1) : d114892 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13744, d114892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13744, d114892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32789 (p : Pattern) (ha : d112688 p = 1) (hb : d115485 p = 1) : d114898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13657 q = 1) (hb : d112688 q = 1) : d13657 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13658 q = 1) (hb : d112688 q = 1) : d114865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32784 q ha hb
    | true =>
      simp only [d13658, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13659 q = 1) (hb : d112688 q = 1) : d114866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13660 q = 1) (hb : d112688 q = 1) : d114867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13660, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13661 q = 1) (hb : d112688 q = 1) : d114868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13667 q = 1) (hb : d112688 q = 1) : d13667 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13668 q = 1) (hb : d112688 q = 1) : d114872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32785 q ha hb
    | true =>
      simp only [d13668, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13669 q = 1) (hb : d112688 q = 1) : d114873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13670 q = 1) (hb : d112688 q = 1) : d114874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13670, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13704 q = 1) (hb : d112688 q = 1) : d114887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32787 q ha hb
    | true =>
      simp only [d13704, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32782 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115481 q = 1) : d114888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115481, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d13745 q = 1) (hb : d112688 q = 1) : d114893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32788 q ha hb
    | true =>
      simp only [d13745, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13746 q = 1) (hb : d112688 q = 1) : d114894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13746, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115482 q = 1) : d114895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115482, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115483 q = 1) : d114896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115483, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115484 q = 1) : d114897 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115484, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115485 q = 1) : d114898 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115485, d114898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115485, d114898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro32790 (p : Pattern) (ha : d13751 p = 1) (hb : d112688 p = 1) : d114899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32776 q ha hb
    | true =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13628 q = 1) (hb : d112688 q = 1) : d114842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13628, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13654 q = 1) (hb : d112688 q = 1) : d114863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13751 q = 1) (hb : d112688 q = 1) : d114899 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13751, d114899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13751, d114899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32791 (p : Pattern) (ha : d13757 p = 1) (hb : d112688 p = 1) : d114904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32776 q ha hb
    | true =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13662 q = 1) (hb : d112688 q = 1) : d114869 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13663 q = 1) (hb : d112688 q = 1) : d114870 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13663, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13757 q = 1) (hb : d112688 q = 1) : d114904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13757, d114904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13757, d114904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32792 (p : Pattern) (ha : d13762 p = 1) (hb : d112688 p = 1) : d114908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d112688 q = 1) : d114881 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32786 q ha hb
    | true =>
      simp only [d13690, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d112688 q = 1) : d114882 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32781 q ha hb
    | true =>
      simp only [d13694, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d112688 q = 1) : d114883 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d112688 q = 1) : d114884 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d112688 q = 1) : d114885 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13762 q = 1) (hb : d112688 q = 1) : d114908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13762, d114908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13762, d114908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32793 (p : Pattern) (ha : d13763 p = 1) (hb : d112688 p = 1) : d114853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32781 q ha hb
    | true =>
      simp only [d13694, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13700 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13701 q = 1) (hb : d112688 q = 1) : d114842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13701, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13702 q = 1) (hb : d112688 q = 1) : d114843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13702, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13763 q = 1) (hb : d112688 q = 1) : d114853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13763, d114853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13763, d114853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32794 (p : Pattern) (ha : d13769 p = 1) (hb : d112688 p = 1) : d114911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32776 q ha hb
    | true =>
      simp only [d13621, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d112688 q = 1) : d114889 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d112688 q = 1) : d114890 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d112688 q = 1) : d114891 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13769 q = 1) (hb : d112688 q = 1) : d114911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13769, d114911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13769, d114911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32795 (p : Pattern) (ha : d112688 p = 1) (hb : d115490 p = 1) : d114917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13657 q = 1) (hb : d112688 q = 1) : d13657 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13658 q = 1) (hb : d112688 q = 1) : d114865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32784 q ha hb
    | true =>
      simp only [d13658, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13659 q = 1) (hb : d112688 q = 1) : d114866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13660 q = 1) (hb : d112688 q = 1) : d114867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13660, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13661 q = 1) (hb : d112688 q = 1) : d114868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13667 q = 1) (hb : d112688 q = 1) : d13667 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13668 q = 1) (hb : d112688 q = 1) : d114872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32785 q ha hb
    | true =>
      simp only [d13668, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13669 q = 1) (hb : d112688 q = 1) : d114873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13670 q = 1) (hb : d112688 q = 1) : d114874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13670, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13704 q = 1) (hb : d112688 q = 1) : d114887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32787 q ha hb
    | true =>
      simp only [d13704, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32782 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115481 q = 1) : d114888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115481, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d13745 q = 1) (hb : d112688 q = 1) : d114893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32788 q ha hb
    | true =>
      simp only [d13745, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13746 q = 1) (hb : d112688 q = 1) : d114894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13746, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115482 q = 1) : d114895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115482, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115483 q = 1) : d114896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115483, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115484 q = 1) : d114897 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115484, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13752 q = 1) (hb : d112688 q = 1) : d13752 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d13753 q = 1) (hb : d112688 q = 1) : d114900 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13753, d114900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32790 q ha hb
    | true =>
      simp only [d13753, d114900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13754 q = 1) (hb : d112688 q = 1) : d114901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13754, d114901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13754, d114901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d13755 q = 1) (hb : d112688 q = 1) : d114902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13755, d114902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d13755, d114902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d13756 q = 1) (hb : d112688 q = 1) : d114903 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13756, d114903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13756, d114903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13758 q = 1) (hb : d112688 q = 1) : d13758 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d13759 q = 1) (hb : d112688 q = 1) : d114905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13759, d114905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32791 q ha hb
    | true =>
      simp only [d13759, d114905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d13760 q = 1) (hb : d112688 q = 1) : d114906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13760, d114906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13760, d114906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d13761 q = 1) (hb : d112688 q = 1) : d114907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13761, d114907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13761, d114907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d13764 q = 1) (hb : d112688 q = 1) : d114909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32792 q ha hb
    | true =>
      simp only [d13764, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32793 q ha hb
  have h27 (q : Pattern) (ha : d112688 q = 1) (hb : d115486 q = 1) : d114910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d115486, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d13770 q = 1) (hb : d112688 q = 1) : d114912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32794 q ha hb
    | true =>
      simp only [d13770, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d13771 q = 1) (hb : d112688 q = 1) : d114913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d13771, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d112688 q = 1) (hb : d115487 q = 1) : d114914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115487, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d112688 q = 1) (hb : d115488 q = 1) : d114915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115488, d114915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d115488, d114915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d112688 q = 1) (hb : d115489 q = 1) : d114916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115489, d114916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115489, d114916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d112688 q = 1) (hb : d115490 q = 1) : d114917 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115490, d114917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115490, d114917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro32796 (p : Pattern) (ha : d112688 p = 1) (hb : d115497 p = 1) : d114926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13764 q = 1) (hb : d112688 q = 1) : d114909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32792 q ha hb
    | true =>
      simp only [d13764, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32793 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115486 q = 1) : d114910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115486, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13770 q = 1) (hb : d112688 q = 1) : d114912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32794 q ha hb
    | true =>
      simp only [d13770, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13771 q = 1) (hb : d112688 q = 1) : d114913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13771, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115487 q = 1) : d114914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115487, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115495 q = 1) : d114924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115495, d114924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115495, d114924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115496 q = 1) : d114925 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115496, d114925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115496, d114925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115497 q = 1) : d114926 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115497, d114926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115497, d114926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32797 (p : Pattern) (ha : d13832 p = 1) (hb : d112688 p = 1) : d114937 p = 1 := by
  have h0 (q : Pattern) (ha : d13812 q = 1) (hb : d94753 q = 1) : d13812 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13809 q = 1) (hb : d94753 q = 1) : d13809 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13822 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13823 q = 1) (hb : d112686 q = 1) : d114932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13823, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13823, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d13824 q = 1) (hb : d112686 q = 1) : d114933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13824, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13824, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13825 q = 1) (hb : d112686 q = 1) : d114934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13825, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13825, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13826 q = 1) (hb : d112687 q = 1) : d114935 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13826, d112687, d114935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13826, d112687, d114935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13830 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13831 q = 1) (hb : d112688 q = 1) : d114936 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13831, d112688, d114936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13831, d112688, d114936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13832 q = 1) (hb : d112688 q = 1) : d114937 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13832, d114937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13832, d114937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32798 (p : Pattern) (ha : d13836 p = 1) (hb : d112688 p = 1) : d114942 p = 1 := by
  have h0 (q : Pattern) (ha : d13829 q = 1) (hb : d94753 q = 1) : d13829 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6642 q = 1) (hb : d94753 q = 1) : d6642 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6648 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6649 q = 1) (hb : d112686 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6649, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6650 q = 1) (hb : d112686 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6650, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6651 q = 1) (hb : d112686 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6651, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13830 q = 1) (hb : d112687 q = 1) : d114940 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d112687, d114940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13830, d112687, d114940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d6652 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13835 q = 1) (hb : d112688 q = 1) : d114941 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13835, d112688, d114941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13835, d112688, d114941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13836 q = 1) (hb : d112688 q = 1) : d114942 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13836, d114942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13836, d114942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32799 (p : Pattern) (ha : d13842 p = 1) (hb : d112688 p = 1) : d114948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13833 q = 1) (hb : d112688 q = 1) : d114938 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13833, d114938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32797 q ha hb
    | true =>
      simp only [d13833, d114938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13834 q = 1) (hb : d112688 q = 1) : d114939 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13834, d114939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13834, d114939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13837 q = 1) (hb : d112688 q = 1) : d114943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32798 q ha hb
    | true =>
      simp only [d13837, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13838 q = 1) (hb : d112688 q = 1) : d114944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13839 q = 1) (hb : d112688 q = 1) : d114945 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13839, d114945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13839, d114945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13840 q = 1) (hb : d112688 q = 1) : d114946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13840, d114946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13840, d114946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13841 q = 1) (hb : d112688 q = 1) : d114947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13841, d114947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13841, d114947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13842 q = 1) (hb : d112688 q = 1) : d114948 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13842, d114948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13842, d114948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32800 (p : Pattern) (ha : d13855 p = 1) (hb : d112688 p = 1) : d114952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13837 q = 1) (hb : d112688 q = 1) : d114943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32798 q ha hb
    | true =>
      simp only [d13837, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13838 q = 1) (hb : d112688 q = 1) : d114944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13851 q = 1) (hb : d112688 q = 1) : d13851 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13852 q = 1) (hb : d112688 q = 1) : d114949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13852, d114949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13852, d114949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13853 q = 1) (hb : d112688 q = 1) : d114950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13853, d114950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13853, d114950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13854 q = 1) (hb : d112688 q = 1) : d114951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13854, d114951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13854, d114951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13855 q = 1) (hb : d112688 q = 1) : d114952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13855, d114952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13855, d114952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro32801 (p : Pattern) (ha : d13896 p = 1) (hb : d112688 p = 1) : d114942 p = 1 := by
  have h0 (q : Pattern) (ha : d13829 q = 1) (hb : d94753 q = 1) : d13829 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6642 q = 1) (hb : d94753 q = 1) : d6642 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6648 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6649 q = 1) (hb : d112686 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6649, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6650 q = 1) (hb : d112686 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6650, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6651 q = 1) (hb : d112686 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6651, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13830 q = 1) (hb : d112687 q = 1) : d114940 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d112687, d114940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13830, d112687, d114940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13847 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13895 q = 1) (hb : d112688 q = 1) : d114941 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13895, d112688, d114941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13895, d112688, d114941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13896 q = 1) (hb : d112688 q = 1) : d114942 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13896, d114942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13896, d114942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32802 (p : Pattern) (ha : d13902 p = 1) (hb : d112688 p = 1) : d114958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d112688 q = 1) : d114943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32801 q ha hb
    | true =>
      simp only [d13897, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d112688 q = 1) : d114944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13899 q = 1) (hb : d112688 q = 1) : d114955 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13899, d114955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13899, d114955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13900 q = 1) (hb : d112688 q = 1) : d114956 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13900, d114956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13900, d114956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13901 q = 1) (hb : d112688 q = 1) : d114957 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13901, d114957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13901, d114957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13902 q = 1) (hb : d112688 q = 1) : d114958 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13902, d114958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13902, d114958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32803 (p : Pattern) (ha : d112688 p = 1) (hb : d115507 p = 1) : d114964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13856 q = 1) (hb : d112688 q = 1) : d114953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13856, d114953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32799 q ha hb
    | true =>
      simp only [d13856, d114953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32800 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115503 q = 1) : d114954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d114954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115503, d114954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13903 q = 1) (hb : d112688 q = 1) : d114959 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13903, d114959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32802 q ha hb
    | true =>
      simp only [d13903, d114959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13904 q = 1) (hb : d112688 q = 1) : d114960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13904, d114960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13904, d114960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115504 q = 1) : d114961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d114961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115504, d114961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115505 q = 1) : d114962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d114962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115505, d114962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115506 q = 1) : d114963 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d114963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115506, d114963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115507 q = 1) : d114964 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d114964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115507, d114964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32804 (p : Pattern) (ha : d112688 p = 1) (hb : d115513 p = 1) : d114970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13641 q = 1) (hb : d112688 q = 1) : d114851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13641, d114851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13641, d114851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32778 q ha hb
  have h2 (q : Pattern) (ha : d13642 q = 1) (hb : d112688 q = 1) : d114852 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13642, d114852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13642, d114852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13651 q = 1) (hb : d112688 q = 1) : d114860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32778 q ha hb
    | true =>
      simp only [d13651, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32780 q ha hb
  have h4 (q : Pattern) (ha : d13652 q = 1) (hb : d112688 q = 1) : d114861 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13652, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13653 q = 1) (hb : d112688 q = 1) : d114862 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13653, d114862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13653, d114862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115491 q = 1) : d114918 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d114918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32789 q ha hb
    | true =>
      simp only [d115491, d114918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32795 q ha hb
  have h7 (q : Pattern) (ha : d13793 q = 1) (hb : d112688 q = 1) : d13793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13794 q = 1) (hb : d112688 q = 1) : d114920 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13794, d114920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32783 q ha hb
    | true =>
      simp only [d13794, d114920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115492 q = 1) : d114921 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d114921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115492, d114921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d115493 q = 1) : d114922 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d114922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115493, d114922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115494 q = 1) : d114923 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d114923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115494, d114923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d115498 q = 1) : d114927 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d114927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115498, d114927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32796 q ha hb
  have h13 (q : Pattern) (ha : d13803 q = 1) (hb : d112688 q = 1) : d13803 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115499 q = 1) : d114928 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d114928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115499, d114928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115500 q = 1) : d114929 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d114929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115500, d114929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115501 q = 1) : d114930 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d114930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115501, d114930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d112688 q = 1) (hb : d115502 q = 1) : d114931 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d114931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115502, d114931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112688 q = 1) (hb : d115508 q = 1) : d114965 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d114965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115508, d114965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32803 q ha hb
  have h19 (q : Pattern) (ha : d13920 q = 1) (hb : d112688 q = 1) : d13920 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d112688 q = 1) (hb : d115509 q = 1) : d114966 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d114966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115509, d114966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d112688 q = 1) (hb : d115510 q = 1) : d114967 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d114967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115510, d114967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d112688 q = 1) (hb : d115511 q = 1) : d114968 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d114968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115511, d114968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112688 q = 1) (hb : d115512 q = 1) : d114969 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d114969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115512, d114969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d112688 q = 1) (hb : d115513 q = 1) : d114970 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d114970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115513, d114970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro32805 (p : Pattern) (ha : d112688 p = 1) (hb : d115519 p = 1) : d114976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115514 q = 1) : d114971 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d114971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115514, d114971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32804 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115515 q = 1) : d114972 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d114972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115515, d114972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115516 q = 1) : d114973 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d114973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115516, d114973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115517 q = 1) : d114974 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d114974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115517, d114974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115518 q = 1) : d114975 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d114975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115518, d114975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115519 q = 1) : d114976 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d114976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115519, d114976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32806 (p : Pattern) (ha : d112688 p = 1) (hb : d115525 p = 1) : d114982 p = 1 := by
  have h0 (q : Pattern) (ha : d112688 q = 1) (hb : d115354 q = 1) : d114403 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d114403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32663 q ha hb
    | true =>
      simp only [d115354, d114403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32689 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115394 q = 1) : d114545 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d114545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115394, d114545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32715 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115395 q = 1) : d114546 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d114546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d114546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115435 q = 1) : d114688 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d114688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115435, d114688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32745 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115436 q = 1) : d114689 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d114689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115436, d114689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115437 q = 1) : d114690 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d114690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d114690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d115477 q = 1) : d114832 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d114832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115477, d114832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32775 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d115478 q = 1) : d114833 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d114833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115478, d114833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d115479 q = 1) : d114834 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d114834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115479, d114834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d115480 q = 1) : d114835 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d114835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d114835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d115520 q = 1) : d114977 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d114977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115520, d114977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32805 q ha hb
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d115521 q = 1) : d114978 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d114978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115521, d114978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112688 q = 1) (hb : d115522 q = 1) : d114979 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d114979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115522, d114979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d115523 q = 1) : d114980 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d114980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115523, d114980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d115524 q = 1) : d114981 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d114981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d114981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d115525 q = 1) : d114982 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d114982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d114982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro32807 (p : Pattern) (ha : d112688 p = 1) (hb : d115531 p = 1) : d114988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115526 q = 1) : d114983 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d114983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32806 q ha hb
    | true =>
      simp only [d115526, d114983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115527 q = 1) : d114984 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d114984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d114984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115528 q = 1) : d114985 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d114985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d114985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115529 q = 1) : d114986 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d114986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d114986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115530 q = 1) : d114987 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d114987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d114987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115531 q = 1) : d114988 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d114988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d114988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32808 (p : Pattern) (ha : d112688 p = 1) (hb : d115537 p = 1) : d114994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115532 q = 1) : d114989 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d114989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32807 q ha hb
    | true =>
      simp only [d115532, d114989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115533 q = 1) : d114990 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d114990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d114990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115534 q = 1) : d114991 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d114991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d114991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115535 q = 1) : d114992 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d114992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d114992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115536 q = 1) : d114993 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d114993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d114993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115537 q = 1) : d114994 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d114994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d114994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32809 (p : Pattern) (ha : d112688 p = 1) (hb : d115543 p = 1) : d115000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115538 q = 1) : d114995 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d114995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32808 q ha hb
    | true =>
      simp only [d115538, d114995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115539 q = 1) : d114996 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d114996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d114996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115540 q = 1) : d114997 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d114997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d114997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115541 q = 1) : d114998 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d114998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d114998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115542 q = 1) : d114999 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d114999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d114999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115543 q = 1) : d115000 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d115000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d115000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32810 (p : Pattern) (ha : d112688 p = 1) (hb : d115549 p = 1) : d115006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115544 q = 1) : d115001 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d115001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32809 q ha hb
    | true =>
      simp only [d115544, d115001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115545 q = 1) : d115002 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d115002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d115002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115546 q = 1) : d115003 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d115003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d115003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115547 q = 1) : d115004 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d115004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115547, d115004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115548 q = 1) : d115005 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d115005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115548, d115005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115549 q = 1) : d115006 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d115006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115549, d115006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32811 (p : Pattern) (ha : d112688 p = 1) (hb : d115555 p = 1) : d115012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115550 q = 1) : d115007 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d115007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32810 q ha hb
    | true =>
      simp only [d115550, d115007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115551 q = 1) : d115008 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d115008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d115008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115552 q = 1) : d115009 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d115552, d115009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115552, d115009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115553 q = 1) : d115010 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d115010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115553, d115010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115554 q = 1) : d115011 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d115011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115554, d115011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115555 q = 1) : d115012 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d115012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115555, d115012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32812 (p : Pattern) (ha : d112688 p = 1) (hb : d115561 p = 1) : d115018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115556 q = 1) : d115013 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d115013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32811 q ha hb
    | true =>
      simp only [d115556, d115013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115557 q = 1) : d115014 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d115014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d115014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115558 q = 1) : d115015 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d115015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d115015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115559 q = 1) : d115016 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d115016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d115016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115560 q = 1) : d115017 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d115017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d115017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115561 q = 1) : d115018 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d115018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d115018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32813 (p : Pattern) (ha : d112688 p = 1) (hb : d115567 p = 1) : d115024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d115562 q = 1) : d115019 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d115019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32812 q ha hb
    | true =>
      simp only [d115562, d115019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d115563 q = 1) : d115020 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d115020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d115020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d115564 q = 1) : d115021 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d115021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d115021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d115565 q = 1) : d115022 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d115022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d115022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d115566 q = 1) : d115023 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d115023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d115023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d115567 q = 1) : d115024 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d115024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d115024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32814 (p : Pattern) (ha : d83664 p = 1) (hb : d114101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4819 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
    | true =>
      simp only [d4819, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d4820 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12225 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12225, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83663 q = 1) (hb : d114100 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83663, d114100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83663, d114100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83664 q = 1) (hb : d114101 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83664, d114101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83664, d114101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro32815 (p : Pattern) (ha : d83670 p = 1) (hb : d114107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32814 q ha hb
    | true =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d114105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83669 q = 1) (hb : d114106 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83669, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83669, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83670 q = 1) (hb : d114107 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83670, d114107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83670, d114107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32816 (p : Pattern) (ha : d83676 p = 1) (hb : d114113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83671 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32815 q ha hb
    | true =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83672 q = 1) (hb : d114109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83672, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83672, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83673 q = 1) (hb : d114110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83673, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83673, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83674 q = 1) (hb : d114111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83674, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83674, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83675 q = 1) (hb : d114112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83675, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83675, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83676 q = 1) (hb : d114113 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83676, d114113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83676, d114113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32817 (p : Pattern) (ha : d83677 p = 1) (hb : d114114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32814 q ha hb
    | true =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d114105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83669 q = 1) (hb : d114106 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83669, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83669, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83677 q = 1) (hb : d114114 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83677, d114114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83677, d114114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32818 (p : Pattern) (ha : d83683 p = 1) (hb : d114120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83671 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32815 q ha hb
    | true =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83672 q = 1) (hb : d114109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83672, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83672, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83673 q = 1) (hb : d114110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83673, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83673, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83674 q = 1) (hb : d114111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83674, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83674, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83675 q = 1) (hb : d114112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83675, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83675, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d83678 q = 1) (hb : d114115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32817 q ha hb
    | true =>
      simp only [d83678, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83679 q = 1) (hb : d114116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83679, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83679, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d83680 q = 1) (hb : d114117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83680, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83680, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83681 q = 1) (hb : d114118 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83681, d114118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d83681, d114118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83682 q = 1) (hb : d114119 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83682, d114119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d83682, d114119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83683 q = 1) (hb : d114120 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83683, d114120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83683, d114120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32819 (p : Pattern) (ha : d83690 p = 1) (hb : d114127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83678 q = 1) (hb : d114115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32817 q ha hb
    | true =>
      simp only [d83678, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83679 q = 1) (hb : d114116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83679, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83679, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83680 q = 1) (hb : d114117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83680, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83680, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83688 q = 1) (hb : d114125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83688, d114125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83688, d114125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83689 q = 1) (hb : d114126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83689, d114126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83689, d114126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83690 q = 1) (hb : d114127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83690, d114127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83690, d114127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32820 (p : Pattern) (ha : d83697 p = 1) (hb : d114134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6079 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
    | true =>
      simp only [d6079, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d6080 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12259 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12259, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83696 q = 1) (hb : d114133 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83696, d114133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83696, d114133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83697 q = 1) (hb : d114134 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83697, d114134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83697, d114134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro32821 (p : Pattern) (ha : d83703 p = 1) (hb : d114140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83698 q = 1) (hb : d114135 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83698, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32820 q ha hb
    | true =>
      simp only [d83698, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83699 q = 1) (hb : d114136 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83699, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83699, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83700 q = 1) (hb : d114137 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83700, d114137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83700, d114137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83701 q = 1) (hb : d114138 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83701, d114138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83701, d114138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83702 q = 1) (hb : d114139 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83702, d114139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83702, d114139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83703 q = 1) (hb : d114140 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83703, d114140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83703, d114140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32822 (p : Pattern) (ha : d83709 p = 1) (hb : d114146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83704 q = 1) (hb : d114141 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83704, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32821 q ha hb
    | true =>
      simp only [d83704, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83705 q = 1) (hb : d114142 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83705, d114142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83705, d114142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83706 q = 1) (hb : d114143 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83706, d114143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83706, d114143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83707 q = 1) (hb : d114144 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83707, d114144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83707, d114144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83708 q = 1) (hb : d114145 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83708, d114145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83708, d114145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83709 q = 1) (hb : d114146 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83709, d114146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83709, d114146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32823 (p : Pattern) (ha : d83715 p = 1) (hb : d114152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83684 q = 1) (hb : d114121 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83684, d114121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32816 q ha hb
    | true =>
      simp only [d83684, d114121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32818 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83685 q = 1) (hb : d114122 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83685, d114122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83685, d114122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d83686 q = 1) (hb : d114123 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83686, d114123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83686, d114123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83687 q = 1) (hb : d114124 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83687, d114124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83687, d114124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83691 q = 1) (hb : d114128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83691, d114128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83691, d114128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32819 q ha hb
  have h12 (q : Pattern) (ha : d83692 q = 1) (hb : d114129 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83692, d114129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83692, d114129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83693 q = 1) (hb : d114130 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83693, d114130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83693, d114130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83694 q = 1) (hb : d114131 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83694, d114131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83694, d114131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83695 q = 1) (hb : d114132 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83695, d114132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83695, d114132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83710 q = 1) (hb : d114147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83710, d114147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83710, d114147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32822 q ha hb
  have h17 (q : Pattern) (ha : d83711 q = 1) (hb : d114148 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83711, d114148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83711, d114148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d83712 q = 1) (hb : d114149 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83712, d114149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83712, d114149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83713 q = 1) (hb : d114150 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83713, d114150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d83713, d114150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d83714 q = 1) (hb : d114151 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83714, d114151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83714, d114151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83715 q = 1) (hb : d114152 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83715, d114152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83715, d114152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro32824 (p : Pattern) (ha : d83725 p = 1) (hb : d114162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32815 q ha hb
    | true =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d114158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d114159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d114160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d114161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83725 q = 1) (hb : d114162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83725, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83725, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32825 (p : Pattern) (ha : d83732 p = 1) (hb : d114169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32815 q ha hb
    | true =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d114158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d114159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d114160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d114161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83678 q = 1) (hb : d114115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32817 q ha hb
    | true =>
      simp only [d83678, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d83728 q = 1) (hb : d114165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83728, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83728, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83729 q = 1) (hb : d114166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83729, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83729, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83730 q = 1) (hb : d114167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83730, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83730, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83731 q = 1) (hb : d114168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83731, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83731, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83732 q = 1) (hb : d114169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83732, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83732, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32826 (p : Pattern) (ha : d83737 p = 1) (hb : d114174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32814 q ha hb
    | true =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d114105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83736 q = 1) (hb : d114173 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83736, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83736, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83737 q = 1) (hb : d114174 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83737, d114174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83737, d114174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32827 (p : Pattern) (ha : d83744 p = 1) (hb : d114181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32814 q ha hb
    | true =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83742 q = 1) (hb : d114179 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83742, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83742, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83743 q = 1) (hb : d114180 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83743, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83743, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83744 q = 1) (hb : d114181 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83744, d114181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83744, d114181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32828 (p : Pattern) (ha : d83749 p = 1) (hb : d114187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22838 q ha hb
    | true =>
      simp only [d12313, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51996 q = 1) (hb : d88338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d51996, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q hb ha
    | true =>
      simp only [d51996, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51997 q = 1) (hb : d88339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d51997, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51997, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51998 q = 1) (hb : d88340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d51998, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51998, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52127 q = 1) (hb : d114185 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52127, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52127, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83748 q = 1) (hb : d114186 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83748, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83748, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83749 q = 1) (hb : d114187 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83749, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83749, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32829 (p : Pattern) (ha : d83755 p = 1) (hb : d114193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83665 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32814 q ha hb
    | true =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83666 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83752 q = 1) (hb : d114190 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83752, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83752, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83753 q = 1) (hb : d114191 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83753, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83753, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83754 q = 1) (hb : d114192 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83754, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83754, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83755 q = 1) (hb : d114193 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83755, d114193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83755, d114193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32830 (p : Pattern) (ha : d83761 p = 1) (hb : d114199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32814 q ha hb
    | true =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83758 q = 1) (hb : d114196 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83758, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83758, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83759 q = 1) (hb : d114197 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83759, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83759, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83760 q = 1) (hb : d114198 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83760, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83760, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83761 q = 1) (hb : d114199 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83761, d114199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83761, d114199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32831 (p : Pattern) (ha : d83767 p = 1) (hb : d114205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83738 q = 1) (hb : d114175 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83738, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32826 q ha hb
    | true =>
      simp only [d83738, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d83739 q = 1) (hb : d114176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83739, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83739, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83740 q = 1) (hb : d114177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83740, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83740, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83741 q = 1) (hb : d114178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83741, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83741, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83745 q = 1) (hb : d114182 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83745, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32827 q ha hb
    | true =>
      simp only [d83745, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d83746 q = 1) (hb : d114183 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83746, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83746, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83747 q = 1) (hb : d114184 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83747, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83747, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83756 q = 1) (hb : d114194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83756, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32829 q ha hb
    | true =>
      simp only [d83756, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32815 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83757 q = 1) (hb : d114195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83757, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d83762 q = 1) (hb : d114200 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83762, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32830 q ha hb
    | true =>
      simp only [d83762, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83763 q = 1) (hb : d114201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83763, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83763, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83764 q = 1) (hb : d114202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83764, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83765 q = 1) (hb : d114203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83765, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83766 q = 1) (hb : d114204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83766, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83767 q = 1) (hb : d114205 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83767, d114205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83767, d114205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32832 (p : Pattern) (ha : d83768 p = 1) (hb : d114206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32814 q ha hb
    | true =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d114105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83736 q = 1) (hb : d114173 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83736, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83736, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83768 q = 1) (hb : d114206 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83768, d114206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83768, d114206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32833 (p : Pattern) (ha : d83773 p = 1) (hb : d114211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32814 q ha hb
    | true =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d114104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83667, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83742 q = 1) (hb : d114179 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83742, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83742, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83743 q = 1) (hb : d114180 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83743, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83743, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83773 q = 1) (hb : d114211 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83773, d114211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83773, d114211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32834 (p : Pattern) (ha : d83777 p = 1) (hb : d114215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83665 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32814 q ha hb
    | true =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83666 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83752 q = 1) (hb : d114190 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83752, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83752, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83753 q = 1) (hb : d114191 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83753, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83753, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83754 q = 1) (hb : d114192 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83754, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83754, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83777 q = 1) (hb : d114215 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83777, d114215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83777, d114215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32835 (p : Pattern) (ha : d83780 p = 1) (hb : d114218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83665 q = 1) (hb : d114102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32814 q ha hb
    | true =>
      simp only [d83665, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83666 q = 1) (hb : d114103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83666, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83758 q = 1) (hb : d114196 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83758, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83758, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83759 q = 1) (hb : d114197 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83759, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83759, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83760 q = 1) (hb : d114198 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83760, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83760, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83780 q = 1) (hb : d114218 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83780, d114218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83780, d114218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32836 (p : Pattern) (ha : d83786 p = 1) (hb : d114224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83738 q = 1) (hb : d114175 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83738, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32826 q ha hb
    | true =>
      simp only [d83738, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d83739 q = 1) (hb : d114176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83739, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83739, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83740 q = 1) (hb : d114177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83740, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83740, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83741 q = 1) (hb : d114178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83741, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83741, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83745 q = 1) (hb : d114182 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83745, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32827 q ha hb
    | true =>
      simp only [d83745, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d83746 q = 1) (hb : d114183 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83746, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83746, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83747 q = 1) (hb : d114184 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83747, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83747, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83756 q = 1) (hb : d114194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83756, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32829 q ha hb
    | true =>
      simp only [d83756, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32815 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83757 q = 1) (hb : d114195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83757, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d83762 q = 1) (hb : d114200 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83762, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32830 q ha hb
    | true =>
      simp only [d83762, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83763 q = 1) (hb : d114201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83763, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83763, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83764 q = 1) (hb : d114202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83764, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83765 q = 1) (hb : d114203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83765, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83766 q = 1) (hb : d114204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83766, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83769 q = 1) (hb : d114207 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83769, d114207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32832 q ha hb
    | true =>
      simp only [d83769, d114207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d83770 q = 1) (hb : d114208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83770, d114208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83770, d114208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83771 q = 1) (hb : d114209 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83771, d114209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83771, d114209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83772 q = 1) (hb : d114210 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83772, d114210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83772, d114210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d83774 q = 1) (hb : d114212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83774, d114212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32833 q ha hb
    | true =>
      simp only [d83774, d114212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d83775 q = 1) (hb : d114213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83775, d114213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83775, d114213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d83776 q = 1) (hb : d114214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83776, d114214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83776, d114214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83778 q = 1) (hb : d114216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83778, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32834 q ha hb
    | true =>
      simp only [d83778, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32817 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83779 q = 1) (hb : d114217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83779, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d83781 q = 1) (hb : d114219 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83781, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32835 q ha hb
    | true =>
      simp only [d83781, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d83782 q = 1) (hb : d114220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83782, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d83782, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d83783 q = 1) (hb : d114221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83783, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d83784 q = 1) (hb : d114222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83784, d114222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d83784, d114222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83785 q = 1) (hb : d114223 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83785, d114223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83785, d114223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83786 q = 1) (hb : d114224 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83786, d114224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83786, d114224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32837 (p : Pattern) (ha : d83788 p = 1) (hb : d114226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32815 q ha hb
    | true =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d114158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d114159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d114160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d114161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83788 q = 1) (hb : d114226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83788, d114226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83788, d114226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro32838 (p : Pattern) (ha : d83795 p = 1) (hb : d114233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83778 q = 1) (hb : d114216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83778, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32834 q ha hb
    | true =>
      simp only [d83778, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32817 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83779 q = 1) (hb : d114217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83779, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83781 q = 1) (hb : d114219 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83781, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32835 q ha hb
    | true =>
      simp only [d83781, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83782 q = 1) (hb : d114220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83782, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83782, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83783 q = 1) (hb : d114221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83783, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83793 q = 1) (hb : d114231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83793, d114231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83793, d114231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83794 q = 1) (hb : d114232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83794, d114232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83794, d114232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83795 q = 1) (hb : d114233 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83795, d114233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83795, d114233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32839 (p : Pattern) (ha : d83802 p = 1) (hb : d114241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22850 q ha hb
    | true =>
      simp only [d12387, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52050 q = 1) (hb : d88402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52050, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q hb ha
    | true =>
      simp only [d52050, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52051 q = 1) (hb : d88403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52051, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52051, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52052 q = 1) (hb : d88404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52052, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52052, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52187 q = 1) (hb : d114239 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52187, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52187, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83801 q = 1) (hb : d114240 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83801, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83801, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83802 q = 1) (hb : d114241 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83802, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83802, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32840 (p : Pattern) (ha : d83808 p = 1) (hb : d114247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83803 q = 1) (hb : d114242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32839 q ha hb
    | true =>
      simp only [d83803, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83804 q = 1) (hb : d114243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83698 q = 1) (hb : d114135 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83698, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32820 q ha hb
    | true =>
      simp only [d83698, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83699 q = 1) (hb : d114136 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83699, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83699, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83805 q = 1) (hb : d114244 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83805, d114244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83805, d114244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83806 q = 1) (hb : d114245 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83806, d114245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83806, d114245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83807 q = 1) (hb : d114246 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83807, d114246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83807, d114246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83808 q = 1) (hb : d114247 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83808, d114247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83808, d114247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32841 (p : Pattern) (ha : d83814 p = 1) (hb : d114253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83698 q = 1) (hb : d114135 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83698, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32820 q ha hb
    | true =>
      simp only [d83698, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83699 q = 1) (hb : d114136 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83699, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83699, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83811 q = 1) (hb : d114250 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83811, d114250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83811, d114250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83812 q = 1) (hb : d114251 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83812, d114251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83812, d114251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83813 q = 1) (hb : d114252 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83813, d114252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83813, d114252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83814 q = 1) (hb : d114253 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83814, d114253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83814, d114253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32842 (p : Pattern) (ha : d83820 p = 1) (hb : d114259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83809 q = 1) (hb : d114248 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83809, d114248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32840 q ha hb
    | true =>
      simp only [d83809, d114248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32821 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83810 q = 1) (hb : d114249 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83810, d114249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83810, d114249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83815 q = 1) (hb : d114254 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83815, d114254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32841 q ha hb
    | true =>
      simp only [d83815, d114254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83816 q = 1) (hb : d114255 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83816, d114255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83816, d114255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83817 q = 1) (hb : d114256 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83817, d114256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83817, d114256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83818 q = 1) (hb : d114257 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83818, d114257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83818, d114257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83819 q = 1) (hb : d114258 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83819, d114258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83819, d114258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83820 q = 1) (hb : d114259 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83820, d114259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83820, d114259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32843 (p : Pattern) (ha : d83826 p = 1) (hb : d114265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83726 q = 1) (hb : d114163 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83726, d114163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83726, d114163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32824 q ha hb
  have h2 (q : Pattern) (ha : d83727 q = 1) (hb : d114164 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83727, d114164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83727, d114164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83733 q = 1) (hb : d114170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83733, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32824 q ha hb
    | true =>
      simp only [d83733, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32825 q ha hb
  have h4 (q : Pattern) (ha : d83734 q = 1) (hb : d114171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83734, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83734, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83735 q = 1) (hb : d114172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83735, d114172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83735, d114172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83787 q = 1) (hb : d114225 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83787, d114225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32831 q ha hb
    | true =>
      simp only [d83787, d114225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32836 q ha hb
  have h7 (q : Pattern) (ha : d83789 q = 1) (hb : d114227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83789, d114227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32837 q ha hb
    | true =>
      simp only [d83789, d114227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d83790 q = 1) (hb : d114228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83790, d114228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83790, d114228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83791 q = 1) (hb : d114229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83791, d114229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83791, d114229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83792 q = 1) (hb : d114230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83792, d114230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83792, d114230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83796 q = 1) (hb : d114234 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83796, d114234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83796, d114234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32838 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d83797 q = 1) (hb : d114235 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83797, d114235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83797, d114235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83798 q = 1) (hb : d114236 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83798, d114236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83798, d114236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83799 q = 1) (hb : d114237 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83799, d114237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d83799, d114237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83800 q = 1) (hb : d114238 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83800, d114238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83800, d114238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83821 q = 1) (hb : d114260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83821, d114260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83821, d114260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32842 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d83822 q = 1) (hb : d114261 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83822, d114261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83822, d114261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d83823 q = 1) (hb : d114262 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83823, d114262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83823, d114262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83824 q = 1) (hb : d114263 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83824, d114263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d83824, d114263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83825 q = 1) (hb : d114264 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83825, d114264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83825, d114264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83826 q = 1) (hb : d114265 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83826, d114265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83826, d114265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32844 (p : Pattern) (ha : d83832 p = 1) (hb : d114271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83716 q = 1) (hb : d114153 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83716, d114153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83716, d114153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32823 q ha hb
  have h6 (q : Pattern) (ha : d83717 q = 1) (hb : d114154 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83717, d114154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83717, d114154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83718 q = 1) (hb : d114155 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83718, d114155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83718, d114155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83719 q = 1) (hb : d114156 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83719, d114156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83719, d114156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83720 q = 1) (hb : d114157 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83720, d114157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83720, d114157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83827 q = 1) (hb : d114266 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83827, d114266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83827, d114266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32843 q ha hb
  have h11 (q : Pattern) (ha : d83828 q = 1) (hb : d114267 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83828, d114267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83828, d114267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83829 q = 1) (hb : d114268 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83829, d114268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83829, d114268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83830 q = 1) (hb : d114269 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83830, d114269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83830, d114269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83831 q = 1) (hb : d114270 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83831, d114270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83831, d114270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83832 q = 1) (hb : d114271 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83832, d114271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83832, d114271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32845 (p : Pattern) (ha : d83836 p = 1) (hb : d114275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d114273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83835 q = 1) (hb : d114274 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83835, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83835, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83836 q = 1) (hb : d114275 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83836, d114275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83836, d114275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32846 (p : Pattern) (ha : d83842 p = 1) (hb : d114281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d114276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32845 q ha hb
    | true =>
      simp only [d83837, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d114277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d114278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d114279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d114280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83842 q = 1) (hb : d114281 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83842, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83842, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32847 (p : Pattern) (ha : d83845 p = 1) (hb : d114284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d114273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83835 q = 1) (hb : d114274 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83835, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83835, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83845 q = 1) (hb : d114284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83845, d114284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83845, d114284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32848 (p : Pattern) (ha : d83851 p = 1) (hb : d114290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d114276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32845 q ha hb
    | true =>
      simp only [d83837, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d114277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d114278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d114279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d114280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83846 q = 1) (hb : d114285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83846, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32847 q ha hb
    | true =>
      simp only [d83846, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28705 q hb ha
  have h7 (q : Pattern) (ha : d83847 q = 1) (hb : d114286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83847, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83847, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83848 q = 1) (hb : d114287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83848, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83848, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83849 q = 1) (hb : d114288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83849, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83849, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83850 q = 1) (hb : d114289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83850, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83850, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83851 q = 1) (hb : d114290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83851, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83851, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32849 (p : Pattern) (ha : d83856 p = 1) (hb : d114295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d114273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83855 q = 1) (hb : d114294 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83855, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83855, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83856 q = 1) (hb : d114295 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83856, d114295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83856, d114295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32850 (p : Pattern) (ha : d83863 p = 1) (hb : d114302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83861 q = 1) (hb : d114300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83861, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83861, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83862 q = 1) (hb : d114301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83862, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83862, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83863 q = 1) (hb : d114302 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83863, d114302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83863, d114302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32851 (p : Pattern) (ha : d83868 p = 1) (hb : d114311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12490 q = 1) (hb : d52296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12490, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28720 q ha hb
    | true =>
      simp only [d12490, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22838 q ha hb
  have h2 (q : Pattern) (ha : d12491 q = 1) (hb : d52297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12491, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12491, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12492 q = 1) (hb : d52298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12492, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12492, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52124 q = 1) (hb : d114306 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52124, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22838 q hb ha
    | true =>
      simp only [d52124, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52125 q = 1) (hb : d114307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52125, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52125, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52126 q = 1) (hb : d114308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52126, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52126, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52299 q = 1) (hb : d114309 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52299, d114309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52299, d114309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83867 q = 1) (hb : d114310 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83867, d114310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83867, d114310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83868 q = 1) (hb : d114311 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83868, d114311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83868, d114311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32852 (p : Pattern) (ha : d83874 p = 1) (hb : d114317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83869 q = 1) (hb : d114312 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83869, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32851 q ha hb
    | true =>
      simp only [d83869, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83870 q = 1) (hb : d114313 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83870, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83870, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83871 q = 1) (hb : d114314 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83871, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83871, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83872 q = 1) (hb : d114315 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83872, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83872, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83873 q = 1) (hb : d114316 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83873, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83873, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83874 q = 1) (hb : d114317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83874, d114317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83874, d114317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32853 (p : Pattern) (ha : d83880 p = 1) (hb : d114323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83877 q = 1) (hb : d114320 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83877, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83877, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83878 q = 1) (hb : d114321 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83878, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83878, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83879 q = 1) (hb : d114322 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83879, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83879, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83880 q = 1) (hb : d114323 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83880, d114323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83880, d114323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32854 (p : Pattern) (ha : d83886 p = 1) (hb : d114329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83857 q = 1) (hb : d114296 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83857, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32849 q ha hb
    | true =>
      simp only [d83857, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28715 q hb ha
  have h2 (q : Pattern) (ha : d83858 q = 1) (hb : d114297 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83858, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83858, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83859 q = 1) (hb : d114298 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83859, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83859, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83860 q = 1) (hb : d114299 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83860, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83860, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83864 q = 1) (hb : d114303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83864, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32850 q ha hb
    | true =>
      simp only [d83864, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28716 q hb ha
  have h6 (q : Pattern) (ha : d83865 q = 1) (hb : d114304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83865, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83865, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83866 q = 1) (hb : d114305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83866, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83866, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83875 q = 1) (hb : d114318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83875, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32852 q ha hb
    | true =>
      simp only [d83875, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32845 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83876 q = 1) (hb : d114319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83876, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d83881 q = 1) (hb : d114324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83881, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32853 q ha hb
    | true =>
      simp only [d83881, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83882 q = 1) (hb : d114325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83882, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83882, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83883 q = 1) (hb : d114326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83883, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83884 q = 1) (hb : d114327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83884, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83885 q = 1) (hb : d114328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83885, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83886 q = 1) (hb : d114329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83886, d114329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83886, d114329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32855 (p : Pattern) (ha : d83887 p = 1) (hb : d114330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d114273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83855 q = 1) (hb : d114294 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83855, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83855, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83887 q = 1) (hb : d114330 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83887, d114330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83887, d114330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32856 (p : Pattern) (ha : d83892 p = 1) (hb : d114335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d114272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83861 q = 1) (hb : d114300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83861, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83861, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83862 q = 1) (hb : d114301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83862, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83862, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83892 q = 1) (hb : d114335 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83892, d114335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83892, d114335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32857 (p : Pattern) (ha : d83896 p = 1) (hb : d114339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83869 q = 1) (hb : d114312 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83869, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32851 q ha hb
    | true =>
      simp only [d83869, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83870 q = 1) (hb : d114313 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83870, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83870, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83871 q = 1) (hb : d114314 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83871, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83871, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83872 q = 1) (hb : d114315 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83872, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83872, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83873 q = 1) (hb : d114316 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83873, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83873, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83896 q = 1) (hb : d114339 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83896, d114339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83896, d114339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32858 (p : Pattern) (ha : d83899 p = 1) (hb : d114342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d114188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32828 q ha hb
    | true =>
      simp only [d83750, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d114189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83877 q = 1) (hb : d114320 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83877, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83877, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83878 q = 1) (hb : d114321 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83878, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83878, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83879 q = 1) (hb : d114322 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83879, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83879, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83899 q = 1) (hb : d114342 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83899, d114342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83899, d114342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32859 (p : Pattern) (ha : d83905 p = 1) (hb : d114348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83857 q = 1) (hb : d114296 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83857, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32849 q ha hb
    | true =>
      simp only [d83857, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28715 q hb ha
  have h2 (q : Pattern) (ha : d83858 q = 1) (hb : d114297 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83858, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83858, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83859 q = 1) (hb : d114298 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83859, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83859, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83860 q = 1) (hb : d114299 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83860, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83860, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83864 q = 1) (hb : d114303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83864, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32850 q ha hb
    | true =>
      simp only [d83864, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28716 q hb ha
  have h6 (q : Pattern) (ha : d83865 q = 1) (hb : d114304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83865, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83865, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83866 q = 1) (hb : d114305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83866, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83866, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83875 q = 1) (hb : d114318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83875, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32852 q ha hb
    | true =>
      simp only [d83875, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32845 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83876 q = 1) (hb : d114319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83876, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d83881 q = 1) (hb : d114324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83881, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32853 q ha hb
    | true =>
      simp only [d83881, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83882 q = 1) (hb : d114325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83882, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83882, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83883 q = 1) (hb : d114326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83883, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83884 q = 1) (hb : d114327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83884, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83885 q = 1) (hb : d114328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83885, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83888 q = 1) (hb : d114331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83888, d114331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32855 q ha hb
    | true =>
      simp only [d83888, d114331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28726 q hb ha
  have h17 (q : Pattern) (ha : d83889 q = 1) (hb : d114332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83889, d114332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83889, d114332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83890 q = 1) (hb : d114333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83890, d114333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83890, d114333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83891 q = 1) (hb : d114334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83891, d114334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83891, d114334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d83893 q = 1) (hb : d114336 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83893, d114336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32856 q ha hb
    | true =>
      simp only [d83893, d114336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28727 q hb ha
  have h21 (q : Pattern) (ha : d83894 q = 1) (hb : d114337 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83894, d114337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83894, d114337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d83895 q = 1) (hb : d114338 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83895, d114338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83895, d114338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83897 q = 1) (hb : d114340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83897, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32857 q ha hb
    | true =>
      simp only [d83897, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32847 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83898 q = 1) (hb : d114341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83898, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d83900 q = 1) (hb : d114343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83900, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32858 q ha hb
    | true =>
      simp only [d83900, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d83901 q = 1) (hb : d114344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83901, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d83901, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d83902 q = 1) (hb : d114345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83902, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d83903 q = 1) (hb : d114346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83903, d114346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d83903, d114346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83904 q = 1) (hb : d114347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83904, d114347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83904, d114347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83905 q = 1) (hb : d114348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83905, d114348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83905, d114348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32860 (p : Pattern) (ha : d83907 p = 1) (hb : d114350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d114276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32845 q ha hb
    | true =>
      simp only [d83837, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d114277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d114278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d114279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d114280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12569 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q ha hb
    | true =>
      simp only [d12569, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12570 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12571 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12571, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12572 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12573 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83907 q = 1) (hb : d114350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83907, d114350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83907, d114350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro32861 (p : Pattern) (ha : d83914 p = 1) (hb : d114357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83897 q = 1) (hb : d114340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83897, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32857 q ha hb
    | true =>
      simp only [d83897, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32847 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83898 q = 1) (hb : d114341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83898, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83900 q = 1) (hb : d114343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83900, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32858 q ha hb
    | true =>
      simp only [d83900, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83901 q = 1) (hb : d114344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83901, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83901, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83902 q = 1) (hb : d114345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83902, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83912 q = 1) (hb : d114355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83912, d114355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83912, d114355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83913 q = 1) (hb : d114356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83913, d114356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83913, d114356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83914 q = 1) (hb : d114357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83914, d114357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83914, d114357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32862 (p : Pattern) (ha : d83921 p = 1) (hb : d114368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12596 q = 1) (hb : d52369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12596, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28737 q ha hb
    | true =>
      simp only [d12596, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22850 q ha hb
  have h2 (q : Pattern) (ha : d12597 q = 1) (hb : d52370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12597, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12597, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12598 q = 1) (hb : d52371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12598, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12598, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52184 q = 1) (hb : d114363 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52184, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22850 q hb ha
    | true =>
      simp only [d52184, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52185 q = 1) (hb : d114364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52185, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52185, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52186 q = 1) (hb : d114365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52186, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52186, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52372 q = 1) (hb : d114366 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52372, d114366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52372, d114366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83920 q = 1) (hb : d114367 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83920, d114367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83920, d114367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83921 q = 1) (hb : d114368 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83921, d114368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83921, d114368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32863 (p : Pattern) (ha : d83927 p = 1) (hb : d114374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83922 q = 1) (hb : d114369 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83922, d114369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32862 q ha hb
    | true =>
      simp only [d83922, d114369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83923 q = 1) (hb : d114370 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83923, d114370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83923, d114370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83803 q = 1) (hb : d114242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32839 q ha hb
    | true =>
      simp only [d83803, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83804 q = 1) (hb : d114243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83924 q = 1) (hb : d114371 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83924, d114371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83924, d114371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83925 q = 1) (hb : d114372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83925, d114372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83925, d114372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83926 q = 1) (hb : d114373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83926, d114373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83926, d114373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83927 q = 1) (hb : d114374 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83927, d114374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83927, d114374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32864 (p : Pattern) (ha : d83931 p = 1) (hb : d114378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83803 q = 1) (hb : d114242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32839 q ha hb
    | true =>
      simp only [d83803, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83804 q = 1) (hb : d114243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12623 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28708 q ha hb
    | true =>
      simp only [d12623, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12624 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83928 q = 1) (hb : d114375 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83928, d114375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83928, d114375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83929 q = 1) (hb : d114376 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83929, d114376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83929, d114376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83930 q = 1) (hb : d114377 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83930, d114377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83930, d114377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83931 q = 1) (hb : d114378 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83931, d114378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83931, d114378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32865 (p : Pattern) (ha : d83938 p = 1) (hb : d114384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83803 q = 1) (hb : d114242 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32839 q ha hb
    | true =>
      simp only [d83803, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83804 q = 1) (hb : d114243 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83935 q = 1) (hb : d114381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83935, d114381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83935, d114381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83936 q = 1) (hb : d114382 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83936, d114382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83936, d114382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83937 q = 1) (hb : d114383 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83937, d114383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83937, d114383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83938 q = 1) (hb : d114384 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83938, d114384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83938, d114384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32866 (p : Pattern) (ha : d83944 p = 1) (hb : d114390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83932 q = 1) (hb : d114379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83932, d114379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32863 q ha hb
    | true =>
      simp only [d83932, d114379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32864 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83934 q = 1) (hb : d114380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83934, d114380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83934, d114380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83939 q = 1) (hb : d114385 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83939, d114385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32865 q ha hb
    | true =>
      simp only [d83939, d114385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83940 q = 1) (hb : d114386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83940, d114386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83940, d114386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83941 q = 1) (hb : d114387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83941, d114387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83941, d114387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83942 q = 1) (hb : d114388 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83942, d114388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83942, d114388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83943 q = 1) (hb : d114389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83943, d114389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83943, d114389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83944 q = 1) (hb : d114390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83944, d114390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83944, d114390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32867 (p : Pattern) (ha : d83950 p = 1) (hb : d114396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83843 q = 1) (hb : d114282 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83843, d114282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83843, d114282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32846 q ha hb
  have h2 (q : Pattern) (ha : d83844 q = 1) (hb : d114283 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83844, d114283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83844, d114283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83852 q = 1) (hb : d114291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83852, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32846 q ha hb
    | true =>
      simp only [d83852, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32848 q ha hb
  have h4 (q : Pattern) (ha : d83853 q = 1) (hb : d114292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83853, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83853, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83854 q = 1) (hb : d114293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83854, d114293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83854, d114293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83906 q = 1) (hb : d114349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83906, d114349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32854 q ha hb
    | true =>
      simp only [d83906, d114349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32859 q ha hb
  have h7 (q : Pattern) (ha : d83908 q = 1) (hb : d114351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83908, d114351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32860 q ha hb
    | true =>
      simp only [d83908, d114351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28706 q hb ha
  have h8 (q : Pattern) (ha : d83909 q = 1) (hb : d114352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83909, d114352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83909, d114352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83910 q = 1) (hb : d114353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83910, d114353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83910, d114353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83911 q = 1) (hb : d114354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83911, d114354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83911, d114354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83915 q = 1) (hb : d114358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83915, d114358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83915, d114358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32861 q ha hb
  have h12 (q : Pattern) (ha : d12590 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12590, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12590, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28707 q ha hb
  have h13 (q : Pattern) (ha : d83916 q = 1) (hb : d114359 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83916, d114359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83916, d114359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83917 q = 1) (hb : d114360 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83917, d114360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83917, d114360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83918 q = 1) (hb : d114361 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83918, d114361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d83918, d114361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83919 q = 1) (hb : d114362 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83919, d114362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83919, d114362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83945 q = 1) (hb : d114391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83945, d114391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83945, d114391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32866 q ha hb
  have h18 (q : Pattern) (ha : d12675 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12675, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12675, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28710 q ha hb
  have h19 (q : Pattern) (ha : d83946 q = 1) (hb : d114392 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83946, d114392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83946, d114392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d83947 q = 1) (hb : d114393 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83947, d114393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83947, d114393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83948 q = 1) (hb : d114394 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83948, d114394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d83948, d114394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83949 q = 1) (hb : d114395 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83949, d114395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83949, d114395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83950 q = 1) (hb : d114396 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83950, d114396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83950, d114396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32868 (p : Pattern) (ha : d83956 p = 1) (hb : d114402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83951 q = 1) (hb : d114397 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83951, d114397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83951, d114397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32867 q ha hb
  have h2 (q : Pattern) (ha : d83952 q = 1) (hb : d114398 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83952, d114398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83952, d114398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83953 q = 1) (hb : d114399 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83953, d114399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83953, d114399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83954 q = 1) (hb : d114400 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83954, d114400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83954, d114400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83955 q = 1) (hb : d114401 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83955, d114401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83955, d114401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83956 q = 1) (hb : d114402 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83956, d114402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83956, d114402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32869 (p : Pattern) (ha : d83959 p = 1) (hb : d114406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12688 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22866 q ha hb
    | true =>
      simp only [d12688, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10581 q ha hb
  have h2 (q : Pattern) (ha : d12689 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12690 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52440 q = 1) (hb : d88489 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52440, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10581 q hb ha
    | true =>
      simp only [d52440, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52441 q = 1) (hb : d88490 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52441, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52441, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52442 q = 1) (hb : d88491 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52442, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52442, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52443 q = 1) (hb : d114404 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52443, d114404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52443, d114404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83958 q = 1) (hb : d114405 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83958, d114405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83958, d114405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83959 q = 1) (hb : d114406 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83959, d114406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83959, d114406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32870 (p : Pattern) (ha : d83965 p = 1) (hb : d114412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32869 q ha hb
    | true =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28745 q ha hb
    | true =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d114410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83964 q = 1) (hb : d114411 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83964, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83964, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83965 q = 1) (hb : d114412 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83965, d114412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83965, d114412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32871 (p : Pattern) (ha : d83971 p = 1) (hb : d114418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83966 q = 1) (hb : d114413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32870 q ha hb
    | true =>
      simp only [d83966, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28746 q hb ha
  have h2 (q : Pattern) (ha : d83967 q = 1) (hb : d114414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83967, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83967, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83968 q = 1) (hb : d114415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83968, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83968, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83969 q = 1) (hb : d114416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83969, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83969, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83970 q = 1) (hb : d114417 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83970, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83970, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83971 q = 1) (hb : d114418 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83971, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83971, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32872 (p : Pattern) (ha : d83974 p = 1) (hb : d114421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32869 q ha hb
    | true =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28745 q ha hb
    | true =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d114410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83964 q = 1) (hb : d114411 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83964, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83964, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83974 q = 1) (hb : d114421 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83974, d114421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83974, d114421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32873 (p : Pattern) (ha : d83980 p = 1) (hb : d114427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83966 q = 1) (hb : d114413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32870 q ha hb
    | true =>
      simp only [d83966, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28746 q hb ha
  have h2 (q : Pattern) (ha : d83967 q = 1) (hb : d114414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83967, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83967, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83968 q = 1) (hb : d114415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83968, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83968, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83969 q = 1) (hb : d114416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83969, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83969, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83970 q = 1) (hb : d114417 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83970, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83970, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83975 q = 1) (hb : d114422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83975, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32872 q ha hb
    | true =>
      simp only [d83975, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28747 q hb ha
  have h7 (q : Pattern) (ha : d83976 q = 1) (hb : d114423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83976, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83976, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83977 q = 1) (hb : d114424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83977, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83977, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83978 q = 1) (hb : d114425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83978, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83978, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83979 q = 1) (hb : d114426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83979, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83979, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83980 q = 1) (hb : d114427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83980, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83980, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32874 (p : Pattern) (ha : d83985 p = 1) (hb : d114432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32869 q ha hb
    | true =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28745 q ha hb
    | true =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d114410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83984 q = 1) (hb : d114431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83984, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83984, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83985 q = 1) (hb : d114432 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83985, d114432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83985, d114432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32875 (p : Pattern) (ha : d83992 p = 1) (hb : d114439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32869 q ha hb
    | true =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28745 q ha hb
    | true =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83990 q = 1) (hb : d114437 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83990, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83990, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83991 q = 1) (hb : d114438 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83991, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83991, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83992 q = 1) (hb : d114439 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83992, d114439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83992, d114439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32876 (p : Pattern) (ha : d83997 p = 1) (hb : d114448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12745 q = 1) (hb : d52517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12745, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28763 q ha hb
    | true =>
      simp only [d12745, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22866 q ha hb
  have h2 (q : Pattern) (ha : d12746 q = 1) (hb : d52518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12746, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12746, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12747 q = 1) (hb : d52519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12747, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12747, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52436 q = 1) (hb : d114443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52436, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22866 q hb ha
    | true =>
      simp only [d52436, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52437 q = 1) (hb : d114444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52437, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52437, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52438 q = 1) (hb : d114445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52438, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52438, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52520 q = 1) (hb : d114446 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52520, d114446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52520, d114446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83996 q = 1) (hb : d114447 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83996, d114447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83996, d114447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83997 q = 1) (hb : d114448 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83997, d114448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83997, d114448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32877 (p : Pattern) (ha : d84003 p = 1) (hb : d114454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83998 q = 1) (hb : d114449 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83998, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32876 q ha hb
    | true =>
      simp only [d83998, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83999 q = 1) (hb : d114450 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83999, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83999, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83960 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32869 q ha hb
    | true =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83961 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84000 q = 1) (hb : d114451 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84000, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84000, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84001 q = 1) (hb : d114452 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84001, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84001, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84002 q = 1) (hb : d114453 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84002, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84002, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84003 q = 1) (hb : d114454 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84003, d114454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84003, d114454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32878 (p : Pattern) (ha : d84009 p = 1) (hb : d114460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32869 q ha hb
    | true =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84006 q = 1) (hb : d114457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84006, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84006, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84007 q = 1) (hb : d114458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84007, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84007, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84008 q = 1) (hb : d114459 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84008, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84008, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84009 q = 1) (hb : d114460 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84009, d114460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84009, d114460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32879 (p : Pattern) (ha : d84015 p = 1) (hb : d114466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83986 q = 1) (hb : d114433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83986, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32874 q ha hb
    | true =>
      simp only [d83986, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28758 q hb ha
  have h2 (q : Pattern) (ha : d83987 q = 1) (hb : d114434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83987, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83987, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83988 q = 1) (hb : d114435 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83988, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83988, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83989 q = 1) (hb : d114436 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83989, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83989, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83993 q = 1) (hb : d114440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83993, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32875 q ha hb
    | true =>
      simp only [d83993, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28759 q hb ha
  have h6 (q : Pattern) (ha : d83994 q = 1) (hb : d114441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83994, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83994, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83995 q = 1) (hb : d114442 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83995, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83995, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84004 q = 1) (hb : d114455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84004, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32877 q ha hb
    | true =>
      simp only [d84004, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32870 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84005 q = 1) (hb : d114456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84005, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84010 q = 1) (hb : d114461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84010, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32878 q ha hb
    | true =>
      simp only [d84010, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84011 q = 1) (hb : d114462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84011, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84011, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84012 q = 1) (hb : d114463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84012, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84013 q = 1) (hb : d114464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84013, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84014 q = 1) (hb : d114465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84014, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84015 q = 1) (hb : d114466 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84015, d114466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84015, d114466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32880 (p : Pattern) (ha : d84016 p = 1) (hb : d114467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32869 q ha hb
    | true =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28745 q ha hb
    | true =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d114410 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83984 q = 1) (hb : d114431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83984, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83984, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84016 q = 1) (hb : d114467 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84016, d114467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84016, d114467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32881 (p : Pattern) (ha : d84021 p = 1) (hb : d114472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32869 q ha hb
    | true =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28745 q ha hb
    | true =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d114409 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83990 q = 1) (hb : d114437 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83990, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83990, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83991 q = 1) (hb : d114438 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83991, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83991, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84021 q = 1) (hb : d114472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84021, d114472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84021, d114472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32882 (p : Pattern) (ha : d84025 p = 1) (hb : d114476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83998 q = 1) (hb : d114449 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83998, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32876 q ha hb
    | true =>
      simp only [d83998, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83999 q = 1) (hb : d114450 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83999, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83999, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83960 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32869 q ha hb
    | true =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83961 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84000 q = 1) (hb : d114451 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84000, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84000, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84001 q = 1) (hb : d114452 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84001, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84001, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84002 q = 1) (hb : d114453 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84002, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84002, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84025 q = 1) (hb : d114476 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84025, d114476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84025, d114476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32883 (p : Pattern) (ha : d84028 p = 1) (hb : d114479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d114407 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32869 q ha hb
    | true =>
      simp only [d83960, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d114408 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84006 q = 1) (hb : d114457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84006, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84006, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84007 q = 1) (hb : d114458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84007, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84007, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84008 q = 1) (hb : d114459 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84008, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84008, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84028 q = 1) (hb : d114479 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84028, d114479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84028, d114479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32884 (p : Pattern) (ha : d84034 p = 1) (hb : d114485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83986 q = 1) (hb : d114433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83986, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32874 q ha hb
    | true =>
      simp only [d83986, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28758 q hb ha
  have h2 (q : Pattern) (ha : d83987 q = 1) (hb : d114434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83987, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83987, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83988 q = 1) (hb : d114435 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83988, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83988, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83989 q = 1) (hb : d114436 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83989, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83989, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83993 q = 1) (hb : d114440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83993, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32875 q ha hb
    | true =>
      simp only [d83993, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28759 q hb ha
  have h6 (q : Pattern) (ha : d83994 q = 1) (hb : d114441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83994, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83994, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83995 q = 1) (hb : d114442 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83995, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83995, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84004 q = 1) (hb : d114455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84004, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32877 q ha hb
    | true =>
      simp only [d84004, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32870 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84005 q = 1) (hb : d114456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84005, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84010 q = 1) (hb : d114461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84010, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32878 q ha hb
    | true =>
      simp only [d84010, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84011 q = 1) (hb : d114462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84011, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84011, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84012 q = 1) (hb : d114463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84012, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84013 q = 1) (hb : d114464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84013, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84014 q = 1) (hb : d114465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84014, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84017 q = 1) (hb : d114468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84017, d114468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32880 q ha hb
    | true =>
      simp only [d84017, d114468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28769 q hb ha
  have h17 (q : Pattern) (ha : d84018 q = 1) (hb : d114469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84018, d114469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84018, d114469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84019 q = 1) (hb : d114470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84019, d114470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84019, d114470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84020 q = 1) (hb : d114471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84020, d114471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84020, d114471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84022 q = 1) (hb : d114473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84022, d114473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32881 q ha hb
    | true =>
      simp only [d84022, d114473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28770 q hb ha
  have h21 (q : Pattern) (ha : d84023 q = 1) (hb : d114474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84023, d114474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84023, d114474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84024 q = 1) (hb : d114475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84024, d114475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84024, d114475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84026 q = 1) (hb : d114477 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84026, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32882 q ha hb
    | true =>
      simp only [d84026, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32872 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84027 q = 1) (hb : d114478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84027, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84029 q = 1) (hb : d114480 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84029, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32883 q ha hb
    | true =>
      simp only [d84029, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84030 q = 1) (hb : d114481 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84030, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84030, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84031 q = 1) (hb : d114482 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84031, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84032 q = 1) (hb : d114483 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84032, d114483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84032, d114483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84033 q = 1) (hb : d114484 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84033, d114484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84033, d114484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84034 q = 1) (hb : d114485 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84034, d114485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84034, d114485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32885 (p : Pattern) (ha : d84036 p = 1) (hb : d114487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83966 q = 1) (hb : d114413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32870 q ha hb
    | true =>
      simp only [d83966, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28746 q hb ha
  have h2 (q : Pattern) (ha : d83967 q = 1) (hb : d114414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83967, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83967, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83968 q = 1) (hb : d114415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83968, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83968, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83969 q = 1) (hb : d114416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83969, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83969, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83970 q = 1) (hb : d114417 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83970, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83970, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12828 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28746 q ha hb
    | true =>
      simp only [d12828, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12829 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12830 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12830, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12831 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12832 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84036 q = 1) (hb : d114487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84036, d114487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84036, d114487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro32886 (p : Pattern) (ha : d84043 p = 1) (hb : d114494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84026 q = 1) (hb : d114477 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84026, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32882 q ha hb
    | true =>
      simp only [d84026, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32872 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84027 q = 1) (hb : d114478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84027, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84029 q = 1) (hb : d114480 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84029, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32883 q ha hb
    | true =>
      simp only [d84029, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84030 q = 1) (hb : d114481 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84030, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84030, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84031 q = 1) (hb : d114482 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84031, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84041 q = 1) (hb : d114492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84041, d114492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84041, d114492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84042 q = 1) (hb : d114493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84042, d114493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84042, d114493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84043 q = 1) (hb : d114494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84043, d114494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84043, d114494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32887 (p : Pattern) (ha : d84050 p = 1) (hb : d114505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12855 q = 1) (hb : d52596 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12855, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28780 q ha hb
    | true =>
      simp only [d12855, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22880 q ha hb
  have h2 (q : Pattern) (ha : d12856 q = 1) (hb : d52597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12856, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12856, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12857 q = 1) (hb : d52598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12857, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12857, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52601 q = 1) (hb : d114500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52601, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22880 q hb ha
    | true =>
      simp only [d52601, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52602 q = 1) (hb : d114501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52602, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52602, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52603 q = 1) (hb : d114502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52603, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52603, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52604 q = 1) (hb : d114503 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52604, d114503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52604, d114503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84049 q = 1) (hb : d114504 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84049, d114504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84049, d114504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84050 q = 1) (hb : d114505 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84050, d114505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84050, d114505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32888 (p : Pattern) (ha : d84054 p = 1) (hb : d114510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12868 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22880 q ha hb
    | true =>
      simp only [d12868, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10600 q ha hb
  have h2 (q : Pattern) (ha : d12869 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12870 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52606 q = 1) (hb : d88553 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52606, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10600 q hb ha
    | true =>
      simp only [d52606, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52607 q = 1) (hb : d88554 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52607, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52607, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52608 q = 1) (hb : d88555 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52608, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52608, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52609 q = 1) (hb : d114508 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52609, d114508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52609, d114508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84053 q = 1) (hb : d114509 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84053, d114509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84053, d114509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84054 q = 1) (hb : d114510 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84054, d114510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84054, d114510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32889 (p : Pattern) (ha : d84060 p = 1) (hb : d114516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84051 q = 1) (hb : d114506 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84051, d114506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32887 q ha hb
    | true =>
      simp only [d84051, d114506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84052 q = 1) (hb : d114507 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84052, d114507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84052, d114507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84055 q = 1) (hb : d114511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84055, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32888 q ha hb
    | true =>
      simp only [d84055, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84056 q = 1) (hb : d114512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84056, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84056, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84057 q = 1) (hb : d114513 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84057, d114513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84057, d114513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84058 q = 1) (hb : d114514 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84058, d114514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84058, d114514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84059 q = 1) (hb : d114515 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84059, d114515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84059, d114515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84060 q = 1) (hb : d114516 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84060, d114516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84060, d114516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32890 (p : Pattern) (ha : d84064 p = 1) (hb : d114520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84055 q = 1) (hb : d114511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84055, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32888 q ha hb
    | true =>
      simp only [d84055, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84056 q = 1) (hb : d114512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84056, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84056, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12886 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28750 q ha hb
    | true =>
      simp only [d12886, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12887 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84061 q = 1) (hb : d114517 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84061, d114517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84061, d114517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84062 q = 1) (hb : d114518 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84062, d114518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84062, d114518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84063 q = 1) (hb : d114519 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84063, d114519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84063, d114519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84064 q = 1) (hb : d114520 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84064, d114520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84064, d114520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32891 (p : Pattern) (ha : d84071 p = 1) (hb : d114526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84055 q = 1) (hb : d114511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84055, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32888 q ha hb
    | true =>
      simp only [d84055, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84056 q = 1) (hb : d114512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84056, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84056, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84068 q = 1) (hb : d114523 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84068, d114523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84068, d114523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84069 q = 1) (hb : d114524 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84069, d114524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84069, d114524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84070 q = 1) (hb : d114525 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84070, d114525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84070, d114525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84071 q = 1) (hb : d114526 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84071, d114526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84071, d114526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32892 (p : Pattern) (ha : d84077 p = 1) (hb : d114532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84065 q = 1) (hb : d114521 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84065, d114521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32889 q ha hb
    | true =>
      simp only [d84065, d114521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32890 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84066 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84067 q = 1) (hb : d114522 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84067, d114522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84067, d114522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84072 q = 1) (hb : d114527 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84072, d114527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32891 q ha hb
    | true =>
      simp only [d84072, d114527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84073 q = 1) (hb : d114528 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84073, d114528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84073, d114528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84074 q = 1) (hb : d114529 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84074, d114529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84074, d114529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84075 q = 1) (hb : d114530 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84075, d114530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84075, d114530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84076 q = 1) (hb : d114531 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84076, d114531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84076, d114531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84077 q = 1) (hb : d114532 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84077, d114532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84077, d114532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32893 (p : Pattern) (ha : d84083 p = 1) (hb : d114538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83972 q = 1) (hb : d114419 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83972, d114419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83972, d114419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32871 q ha hb
  have h2 (q : Pattern) (ha : d83973 q = 1) (hb : d114420 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83973, d114420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83973, d114420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83981 q = 1) (hb : d114428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83981, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32871 q ha hb
    | true =>
      simp only [d83981, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32873 q ha hb
  have h4 (q : Pattern) (ha : d83982 q = 1) (hb : d114429 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83982, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83982, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83983 q = 1) (hb : d114430 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83983, d114430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83983, d114430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84035 q = 1) (hb : d114486 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84035, d114486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32879 q ha hb
    | true =>
      simp only [d84035, d114486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32884 q ha hb
  have h7 (q : Pattern) (ha : d84037 q = 1) (hb : d114488 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84037, d114488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32885 q ha hb
    | true =>
      simp only [d84037, d114488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28748 q hb ha
  have h8 (q : Pattern) (ha : d84038 q = 1) (hb : d114489 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84038, d114489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84038, d114489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84039 q = 1) (hb : d114490 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84039, d114490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84039, d114490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84040 q = 1) (hb : d114491 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84040, d114491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84040, d114491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84044 q = 1) (hb : d114495 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84044, d114495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84044, d114495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32886 q ha hb
  have h12 (q : Pattern) (ha : d12849 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12849, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12849, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28749 q ha hb
  have h13 (q : Pattern) (ha : d84045 q = 1) (hb : d114496 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84045, d114496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84045, d114496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84046 q = 1) (hb : d114497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84046, d114497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84046, d114497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84047 q = 1) (hb : d114498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84047, d114498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84047, d114498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84048 q = 1) (hb : d114499 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84048, d114499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84048, d114499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84078 q = 1) (hb : d114533 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84078, d114533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84078, d114533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32892 q ha hb
  have h18 (q : Pattern) (ha : d12942 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12942, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12942, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28752 q ha hb
  have h19 (q : Pattern) (ha : d84079 q = 1) (hb : d114534 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84079, d114534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84079, d114534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84080 q = 1) (hb : d114535 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84080, d114535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84080, d114535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84081 q = 1) (hb : d114536 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84081, d114536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84081, d114536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84082 q = 1) (hb : d114537 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84082, d114537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84082, d114537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84083 q = 1) (hb : d114538 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84083, d114538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84083, d114538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32894 (p : Pattern) (ha : d84089 p = 1) (hb : d114544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84084 q = 1) (hb : d114539 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84084, d114539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84084, d114539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32893 q ha hb
  have h2 (q : Pattern) (ha : d84085 q = 1) (hb : d114540 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84085, d114540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84085, d114540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84086 q = 1) (hb : d114541 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84086, d114541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84086, d114541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84087 q = 1) (hb : d114542 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84087, d114542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84087, d114542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84088 q = 1) (hb : d114543 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84088, d114543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84088, d114543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84089 q = 1) (hb : d114544 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84089, d114544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84089, d114544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32895 (p : Pattern) (ha : d84093 p = 1) (hb : d114549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22898 q ha hb
    | true =>
      simp only [d12957, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10613 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52722 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52723 q = 1) (hb : d88641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52723, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10613 q hb ha
    | true =>
      simp only [d52723, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52724 q = 1) (hb : d88642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52724, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52724, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52725 q = 1) (hb : d88643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52725, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52725, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52726 q = 1) (hb : d114547 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52726, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52726, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84092 q = 1) (hb : d114548 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84092, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84092, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84093 q = 1) (hb : d114549 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84093, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84093, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32896 (p : Pattern) (ha : d84099 p = 1) (hb : d114555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32895 q ha hb
    | true =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28790 q ha hb
    | true =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d114553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84098 q = 1) (hb : d114554 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84098, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84098, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84099 q = 1) (hb : d114555 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84099, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84099, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32897 (p : Pattern) (ha : d84105 p = 1) (hb : d114561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84100 q = 1) (hb : d114556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32896 q ha hb
    | true =>
      simp only [d84100, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28791 q hb ha
  have h2 (q : Pattern) (ha : d84101 q = 1) (hb : d114557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84101, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84101, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84102 q = 1) (hb : d114558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84102, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84102, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84103 q = 1) (hb : d114559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84103, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84103, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84104 q = 1) (hb : d114560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84104, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84104, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84105 q = 1) (hb : d114561 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84105, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84105, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32898 (p : Pattern) (ha : d84108 p = 1) (hb : d114564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32895 q ha hb
    | true =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28790 q ha hb
    | true =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d114553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84098 q = 1) (hb : d114554 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84098, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84098, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84108 q = 1) (hb : d114564 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84108, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84108, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32899 (p : Pattern) (ha : d84114 p = 1) (hb : d114570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84100 q = 1) (hb : d114556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32896 q ha hb
    | true =>
      simp only [d84100, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28791 q hb ha
  have h2 (q : Pattern) (ha : d84101 q = 1) (hb : d114557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84101, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84101, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84102 q = 1) (hb : d114558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84102, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84102, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84103 q = 1) (hb : d114559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84103, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84103, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84104 q = 1) (hb : d114560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84104, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84104, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84109 q = 1) (hb : d114565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84109, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32898 q ha hb
    | true =>
      simp only [d84109, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28792 q hb ha
  have h7 (q : Pattern) (ha : d84110 q = 1) (hb : d114566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84110, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84110, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84111 q = 1) (hb : d114567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84111, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84111, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d84112 q = 1) (hb : d114568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84112, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84112, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84113 q = 1) (hb : d114569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84113, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84113, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84114 q = 1) (hb : d114570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84114, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84114, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32900 (p : Pattern) (ha : d84119 p = 1) (hb : d114575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32895 q ha hb
    | true =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28790 q ha hb
    | true =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d114553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84118 q = 1) (hb : d114574 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84118, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84118, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84119 q = 1) (hb : d114575 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84119, d114575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84119, d114575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32901 (p : Pattern) (ha : d84126 p = 1) (hb : d114582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32895 q ha hb
    | true =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28790 q ha hb
    | true =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84124 q = 1) (hb : d114580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84124, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84124, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84125 q = 1) (hb : d114581 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84125, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84125, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84126 q = 1) (hb : d114582 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84126, d114582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84126, d114582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32902 (p : Pattern) (ha : d84131 p = 1) (hb : d114591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13019 q = 1) (hb : d52797 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13019, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28809 q ha hb
    | true =>
      simp only [d13019, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22898 q ha hb
  have h2 (q : Pattern) (ha : d13020 q = 1) (hb : d52798 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13020, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13020, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13021 q = 1) (hb : d52799 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13021, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13021, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52710 q = 1) (hb : d114586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52710, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22898 q hb ha
    | true =>
      simp only [d52710, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52711 q = 1) (hb : d114587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52711, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52711, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52712 q = 1) (hb : d114588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52712, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52712, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52800 q = 1) (hb : d114589 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52800, d114589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52800, d114589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84130 q = 1) (hb : d114590 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84130, d114590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84130, d114590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84131 q = 1) (hb : d114591 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84131, d114591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84131, d114591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32903 (p : Pattern) (ha : d84137 p = 1) (hb : d114597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84132 q = 1) (hb : d114592 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84132, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32902 q ha hb
    | true =>
      simp only [d84132, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84133 q = 1) (hb : d114593 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84133, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84133, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84094 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32895 q ha hb
    | true =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84095 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84134 q = 1) (hb : d114594 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84134, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84134, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84135 q = 1) (hb : d114595 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84135, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84135, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84136 q = 1) (hb : d114596 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84136, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84136, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84137 q = 1) (hb : d114597 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84137, d114597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84137, d114597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32904 (p : Pattern) (ha : d84143 p = 1) (hb : d114603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32895 q ha hb
    | true =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84140 q = 1) (hb : d114600 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84140, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84140, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84141 q = 1) (hb : d114601 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84141, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84141, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84142 q = 1) (hb : d114602 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84142, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84142, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84143 q = 1) (hb : d114603 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84143, d114603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84143, d114603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32905 (p : Pattern) (ha : d84149 p = 1) (hb : d114609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84120 q = 1) (hb : d114576 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84120, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32900 q ha hb
    | true =>
      simp only [d84120, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28804 q hb ha
  have h2 (q : Pattern) (ha : d84121 q = 1) (hb : d114577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84121, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84121, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84122 q = 1) (hb : d114578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84122, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84122, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84123 q = 1) (hb : d114579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84123, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84123, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84127 q = 1) (hb : d114583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84127, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32901 q ha hb
    | true =>
      simp only [d84127, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28805 q hb ha
  have h6 (q : Pattern) (ha : d84128 q = 1) (hb : d114584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84128, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84128, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84129 q = 1) (hb : d114585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84129, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84129, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84138 q = 1) (hb : d114598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84138, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32903 q ha hb
    | true =>
      simp only [d84138, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32896 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84139 q = 1) (hb : d114599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84139, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84144 q = 1) (hb : d114604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84144, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32904 q ha hb
    | true =>
      simp only [d84144, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84145 q = 1) (hb : d114605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84145, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84145, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84146 q = 1) (hb : d114606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84146, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84147 q = 1) (hb : d114607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84147, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84148 q = 1) (hb : d114608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84148, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84149 q = 1) (hb : d114609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84149, d114609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84149, d114609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32906 (p : Pattern) (ha : d84150 p = 1) (hb : d114610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32895 q ha hb
    | true =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28790 q ha hb
    | true =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d114553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84118 q = 1) (hb : d114574 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84118, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84118, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84150 q = 1) (hb : d114610 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84150, d114610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84150, d114610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32907 (p : Pattern) (ha : d84155 p = 1) (hb : d114615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32895 q ha hb
    | true =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28790 q ha hb
    | true =>
      simp only [d12972, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d114552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84124 q = 1) (hb : d114580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84124, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84124, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84125 q = 1) (hb : d114581 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84125, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84125, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84155 q = 1) (hb : d114615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84155, d114615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84155, d114615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32908 (p : Pattern) (ha : d84159 p = 1) (hb : d114619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84132 q = 1) (hb : d114592 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84132, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32902 q ha hb
    | true =>
      simp only [d84132, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84133 q = 1) (hb : d114593 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84133, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84133, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84094 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32895 q ha hb
    | true =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84095 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84134 q = 1) (hb : d114594 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84134, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84134, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84135 q = 1) (hb : d114595 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84135, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84135, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84136 q = 1) (hb : d114596 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84136, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84136, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84159 q = 1) (hb : d114619 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84159, d114619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84159, d114619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32909 (p : Pattern) (ha : d84162 p = 1) (hb : d114622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d114550 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32895 q ha hb
    | true =>
      simp only [d84094, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d114551 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84140 q = 1) (hb : d114600 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84140, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84140, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84141 q = 1) (hb : d114601 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84141, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84141, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84142 q = 1) (hb : d114602 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84142, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84142, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84162 q = 1) (hb : d114622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84162, d114622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84162, d114622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32910 (p : Pattern) (ha : d84168 p = 1) (hb : d114628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84120 q = 1) (hb : d114576 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84120, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32900 q ha hb
    | true =>
      simp only [d84120, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28804 q hb ha
  have h2 (q : Pattern) (ha : d84121 q = 1) (hb : d114577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84121, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84121, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84122 q = 1) (hb : d114578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84122, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84122, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84123 q = 1) (hb : d114579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84123, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84123, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84127 q = 1) (hb : d114583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84127, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32901 q ha hb
    | true =>
      simp only [d84127, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28805 q hb ha
  have h6 (q : Pattern) (ha : d84128 q = 1) (hb : d114584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84128, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84128, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84129 q = 1) (hb : d114585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84129, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84129, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84138 q = 1) (hb : d114598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84138, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32903 q ha hb
    | true =>
      simp only [d84138, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32896 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84139 q = 1) (hb : d114599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84139, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84144 q = 1) (hb : d114604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84144, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32904 q ha hb
    | true =>
      simp only [d84144, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84145 q = 1) (hb : d114605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84145, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84145, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84146 q = 1) (hb : d114606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84146, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84147 q = 1) (hb : d114607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84147, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84148 q = 1) (hb : d114608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84148, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84151 q = 1) (hb : d114611 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84151, d114611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32906 q ha hb
    | true =>
      simp only [d84151, d114611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28815 q hb ha
  have h17 (q : Pattern) (ha : d84152 q = 1) (hb : d114612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84152, d114612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84152, d114612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84153 q = 1) (hb : d114613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84153, d114613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84153, d114613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84154 q = 1) (hb : d114614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84154, d114614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84154, d114614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84156 q = 1) (hb : d114616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84156, d114616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32907 q ha hb
    | true =>
      simp only [d84156, d114616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28816 q hb ha
  have h21 (q : Pattern) (ha : d84157 q = 1) (hb : d114617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84157, d114617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84157, d114617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84158 q = 1) (hb : d114618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84158, d114618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84158, d114618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84160 q = 1) (hb : d114620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84160, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32908 q ha hb
    | true =>
      simp only [d84160, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32898 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84161 q = 1) (hb : d114621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84161, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84163 q = 1) (hb : d114623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84163, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32909 q ha hb
    | true =>
      simp only [d84163, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84164 q = 1) (hb : d114624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84164, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84164, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84165 q = 1) (hb : d114625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84165, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84166 q = 1) (hb : d114626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84166, d114626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84166, d114626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84167 q = 1) (hb : d114627 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84167, d114627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84167, d114627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84168 q = 1) (hb : d114628 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84168, d114628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84168, d114628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32911 (p : Pattern) (ha : d84170 p = 1) (hb : d114630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84100 q = 1) (hb : d114556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32896 q ha hb
    | true =>
      simp only [d84100, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28791 q hb ha
  have h2 (q : Pattern) (ha : d84101 q = 1) (hb : d114557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84101, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84101, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84102 q = 1) (hb : d114558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84102, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84102, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84103 q = 1) (hb : d114559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84103, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84103, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84104 q = 1) (hb : d114560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84104, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84104, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13129 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28791 q ha hb
    | true =>
      simp only [d13129, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13130 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13131 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13131, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13132 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13133 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84170 q = 1) (hb : d114630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84170, d114630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84170, d114630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro32912 (p : Pattern) (ha : d84177 p = 1) (hb : d114637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84160 q = 1) (hb : d114620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84160, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32908 q ha hb
    | true =>
      simp only [d84160, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32898 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84161 q = 1) (hb : d114621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84161, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84163 q = 1) (hb : d114623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84163, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32909 q ha hb
    | true =>
      simp only [d84163, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84164 q = 1) (hb : d114624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84164, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84164, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84165 q = 1) (hb : d114625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84165, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84175 q = 1) (hb : d114635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84175, d114635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84175, d114635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84176 q = 1) (hb : d114636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84176, d114636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84176, d114636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84177 q = 1) (hb : d114637 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84177, d114637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84177, d114637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32913 (p : Pattern) (ha : d84184 p = 1) (hb : d114648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13157 q = 1) (hb : d52885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13157, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28826 q ha hb
    | true =>
      simp only [d13157, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22912 q ha hb
  have h2 (q : Pattern) (ha : d13158 q = 1) (hb : d52886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13158, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13158, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13159 q = 1) (hb : d52887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13159, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13159, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52890 q = 1) (hb : d114643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52890, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22912 q hb ha
    | true =>
      simp only [d52890, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52891 q = 1) (hb : d114644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52891, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52891, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52892 q = 1) (hb : d114645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52892, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52892, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52893 q = 1) (hb : d114646 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52893, d114646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52893, d114646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84183 q = 1) (hb : d114647 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84183, d114647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84183, d114647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84184 q = 1) (hb : d114648 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84184, d114648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84184, d114648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32914 (p : Pattern) (ha : d84188 p = 1) (hb : d114653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22912 q ha hb
    | true =>
      simp only [d13174, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10632 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52899 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52900 q = 1) (hb : d88705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52900, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10632 q hb ha
    | true =>
      simp only [d52900, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52901 q = 1) (hb : d88706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52901, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52901, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52902 q = 1) (hb : d88707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52902, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52902, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52903 q = 1) (hb : d114651 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52903, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52903, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84187 q = 1) (hb : d114652 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84187, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84187, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84188 q = 1) (hb : d114653 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84188, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84188, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32915 (p : Pattern) (ha : d84194 p = 1) (hb : d114659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84185 q = 1) (hb : d114649 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84185, d114649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32913 q ha hb
    | true =>
      simp only [d84185, d114649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84186 q = 1) (hb : d114650 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84186, d114650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84186, d114650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84189 q = 1) (hb : d114654 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84189, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32914 q ha hb
    | true =>
      simp only [d84189, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84190 q = 1) (hb : d114655 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84190, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84190, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84191 q = 1) (hb : d114656 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84191, d114656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84191, d114656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84192 q = 1) (hb : d114657 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84192, d114657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84192, d114657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84193 q = 1) (hb : d114658 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84193, d114658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84193, d114658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84194 q = 1) (hb : d114659 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84194, d114659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84194, d114659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32916 (p : Pattern) (ha : d84198 p = 1) (hb : d114663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84189 q = 1) (hb : d114654 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84189, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32914 q ha hb
    | true =>
      simp only [d84189, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84190 q = 1) (hb : d114655 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84190, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84190, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28796 q ha hb
    | true =>
      simp only [d13197, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84195 q = 1) (hb : d114660 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84195, d114660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84195, d114660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84196 q = 1) (hb : d114661 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84196, d114661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84196, d114661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84197 q = 1) (hb : d114662 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84197, d114662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84197, d114662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84198 q = 1) (hb : d114663 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84198, d114663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84198, d114663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32917 (p : Pattern) (ha : d84205 p = 1) (hb : d114669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84189 q = 1) (hb : d114654 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84189, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32914 q ha hb
    | true =>
      simp only [d84189, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84190 q = 1) (hb : d114655 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84190, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84190, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84202 q = 1) (hb : d114666 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84202, d114666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84202, d114666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84203 q = 1) (hb : d114667 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84203, d114667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84203, d114667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84204 q = 1) (hb : d114668 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84204, d114668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84204, d114668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84205 q = 1) (hb : d114669 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84205, d114669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84205, d114669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32918 (p : Pattern) (ha : d84211 p = 1) (hb : d114675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84199 q = 1) (hb : d114664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84199, d114664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32915 q ha hb
    | true =>
      simp only [d84199, d114664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32916 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84200 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84201 q = 1) (hb : d114665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84201, d114665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84201, d114665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84206 q = 1) (hb : d114670 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84206, d114670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32917 q ha hb
    | true =>
      simp only [d84206, d114670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84207 q = 1) (hb : d114671 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84207, d114671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84207, d114671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84208 q = 1) (hb : d114672 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84208, d114672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84208, d114672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84209 q = 1) (hb : d114673 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84209, d114673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84209, d114673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84210 q = 1) (hb : d114674 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84210, d114674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84210, d114674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84211 q = 1) (hb : d114675 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84211, d114675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84211, d114675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32919 (p : Pattern) (ha : d84217 p = 1) (hb : d114681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84106 q = 1) (hb : d114562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84106, d114562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84106, d114562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32897 q ha hb
  have h2 (q : Pattern) (ha : d84107 q = 1) (hb : d114563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84107, d114563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84107, d114563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84115 q = 1) (hb : d114571 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84115, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32897 q ha hb
    | true =>
      simp only [d84115, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32899 q ha hb
  have h4 (q : Pattern) (ha : d84116 q = 1) (hb : d114572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84116, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84116, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84117 q = 1) (hb : d114573 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84117, d114573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84117, d114573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84169 q = 1) (hb : d114629 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84169, d114629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32905 q ha hb
    | true =>
      simp only [d84169, d114629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32910 q ha hb
  have h7 (q : Pattern) (ha : d84171 q = 1) (hb : d114631 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84171, d114631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32911 q ha hb
    | true =>
      simp only [d84171, d114631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28793 q hb ha
  have h8 (q : Pattern) (ha : d84172 q = 1) (hb : d114632 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84172, d114632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84172, d114632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84173 q = 1) (hb : d114633 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84173, d114633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84173, d114633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84174 q = 1) (hb : d114634 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84174, d114634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84174, d114634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84178 q = 1) (hb : d114638 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84178, d114638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84178, d114638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32912 q ha hb
  have h12 (q : Pattern) (ha : d13150 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13150, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13150, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28794 q ha hb
  have h13 (q : Pattern) (ha : d84179 q = 1) (hb : d114639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84179, d114639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84179, d114639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84180 q = 1) (hb : d114640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84180, d114640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84180, d114640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84181 q = 1) (hb : d114641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84181, d114641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84181, d114641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84182 q = 1) (hb : d114642 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84182, d114642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84182, d114642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84212 q = 1) (hb : d114676 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84212, d114676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84212, d114676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32918 q ha hb
  have h18 (q : Pattern) (ha : d13267 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13267, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13267, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28798 q ha hb
  have h19 (q : Pattern) (ha : d84213 q = 1) (hb : d114677 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84213, d114677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84213, d114677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84214 q = 1) (hb : d114678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84214, d114678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84214, d114678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84215 q = 1) (hb : d114679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84215, d114679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84215, d114679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84216 q = 1) (hb : d114680 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84216, d114680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84216, d114680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84217 q = 1) (hb : d114681 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84217, d114681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84217, d114681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32920 (p : Pattern) (ha : d84223 p = 1) (hb : d114687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84218 q = 1) (hb : d114682 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84218, d114682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84218, d114682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32919 q ha hb
  have h2 (q : Pattern) (ha : d84219 q = 1) (hb : d114683 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84219, d114683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84219, d114683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84220 q = 1) (hb : d114684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84220, d114684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84220, d114684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84221 q = 1) (hb : d114685 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84221, d114685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84221, d114685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84222 q = 1) (hb : d114686 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84222, d114686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84222, d114686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84223 q = 1) (hb : d114687 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84223, d114687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84223, d114687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32921 (p : Pattern) (ha : d84228 p = 1) (hb : d114693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22930 q ha hb
    | true =>
      simp only [d13283, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10645 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53043 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53044 q = 1) (hb : d88794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53044, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10645 q hb ha
    | true =>
      simp only [d53044, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53045 q = 1) (hb : d88795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53045, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53045, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53046 q = 1) (hb : d88796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53046, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53046, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53047 q = 1) (hb : d114691 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53047, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53047, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84227 q = 1) (hb : d114692 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84227, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84227, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84228 q = 1) (hb : d114693 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84228, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84228, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32922 (p : Pattern) (ha : d84234 p = 1) (hb : d114699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32921 q ha hb
    | true =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28836 q ha hb
    | true =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d114697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84233 q = 1) (hb : d114698 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84233, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84233, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84234 q = 1) (hb : d114699 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84234, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84234, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32923 (p : Pattern) (ha : d84240 p = 1) (hb : d114705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84235 q = 1) (hb : d114700 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32922 q ha hb
    | true =>
      simp only [d84235, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28837 q hb ha
  have h2 (q : Pattern) (ha : d84236 q = 1) (hb : d114701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84236, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84236, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84237 q = 1) (hb : d114702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84237, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84237, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84238 q = 1) (hb : d114703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84238, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84238, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84239 q = 1) (hb : d114704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84239, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84239, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84240 q = 1) (hb : d114705 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84240, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84240, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32924 (p : Pattern) (ha : d84243 p = 1) (hb : d114708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32921 q ha hb
    | true =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28836 q ha hb
    | true =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d114697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84233 q = 1) (hb : d114698 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84233, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84233, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84243 q = 1) (hb : d114708 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84243, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84243, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32925 (p : Pattern) (ha : d84249 p = 1) (hb : d114714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84235 q = 1) (hb : d114700 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32922 q ha hb
    | true =>
      simp only [d84235, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28837 q hb ha
  have h2 (q : Pattern) (ha : d84236 q = 1) (hb : d114701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84236, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84236, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84237 q = 1) (hb : d114702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84237, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84237, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84238 q = 1) (hb : d114703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84238, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84238, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84239 q = 1) (hb : d114704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84239, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84239, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84244 q = 1) (hb : d114709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84244, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32924 q ha hb
    | true =>
      simp only [d84244, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28838 q hb ha
  have h7 (q : Pattern) (ha : d84245 q = 1) (hb : d114710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84245, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84245, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84246 q = 1) (hb : d114711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84246, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84246, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d84247 q = 1) (hb : d114712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84247, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84247, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84248 q = 1) (hb : d114713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84248, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84248, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84249 q = 1) (hb : d114714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84249, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84249, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32926 (p : Pattern) (ha : d84254 p = 1) (hb : d114719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32921 q ha hb
    | true =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28836 q ha hb
    | true =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d114697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84253 q = 1) (hb : d114718 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84253, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84253, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84254 q = 1) (hb : d114719 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84254, d114719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84254, d114719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32927 (p : Pattern) (ha : d84261 p = 1) (hb : d114726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32921 q ha hb
    | true =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28836 q ha hb
    | true =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84259 q = 1) (hb : d114724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84259, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84259, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84260 q = 1) (hb : d114725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84260, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84260, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84261 q = 1) (hb : d114726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84261, d114726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84261, d114726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32928 (p : Pattern) (ha : d84266 p = 1) (hb : d114735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13345 q = 1) (hb : d53112 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13345, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28855 q ha hb
    | true =>
      simp only [d13345, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22930 q ha hb
  have h2 (q : Pattern) (ha : d13346 q = 1) (hb : d53113 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13346, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13346, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13347 q = 1) (hb : d53114 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13347, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13347, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53031 q = 1) (hb : d114730 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53031, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22930 q hb ha
    | true =>
      simp only [d53031, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53032 q = 1) (hb : d114731 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53032, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53032, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53033 q = 1) (hb : d114732 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53033, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53033, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53115 q = 1) (hb : d114733 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53115, d114733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53115, d114733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84265 q = 1) (hb : d114734 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84265, d114734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84265, d114734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84266 q = 1) (hb : d114735 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84266, d114735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84266, d114735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32929 (p : Pattern) (ha : d84272 p = 1) (hb : d114741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84267 q = 1) (hb : d114736 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84267, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32928 q ha hb
    | true =>
      simp only [d84267, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84268 q = 1) (hb : d114737 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84268, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84268, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84229 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32921 q ha hb
    | true =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84230 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84269 q = 1) (hb : d114738 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84269, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84269, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84270 q = 1) (hb : d114739 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84270, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84270, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84271 q = 1) (hb : d114740 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84271, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84271, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84272 q = 1) (hb : d114741 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84272, d114741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84272, d114741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32930 (p : Pattern) (ha : d84278 p = 1) (hb : d114747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32921 q ha hb
    | true =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84275 q = 1) (hb : d114744 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84275, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84275, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84276 q = 1) (hb : d114745 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84276, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84276, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84277 q = 1) (hb : d114746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84277, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84277, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84278 q = 1) (hb : d114747 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84278, d114747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84278, d114747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32931 (p : Pattern) (ha : d84284 p = 1) (hb : d114753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84255 q = 1) (hb : d114720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84255, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32926 q ha hb
    | true =>
      simp only [d84255, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28850 q hb ha
  have h2 (q : Pattern) (ha : d84256 q = 1) (hb : d114721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84256, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84256, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84257 q = 1) (hb : d114722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84257, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84257, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84258 q = 1) (hb : d114723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84258, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84258, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84262 q = 1) (hb : d114727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84262, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32927 q ha hb
    | true =>
      simp only [d84262, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28851 q hb ha
  have h6 (q : Pattern) (ha : d84263 q = 1) (hb : d114728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84263, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84263, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84264 q = 1) (hb : d114729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84264, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84264, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84273 q = 1) (hb : d114742 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84273, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32929 q ha hb
    | true =>
      simp only [d84273, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32922 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84274 q = 1) (hb : d114743 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84274, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84279 q = 1) (hb : d114748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84279, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32930 q ha hb
    | true =>
      simp only [d84279, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84280 q = 1) (hb : d114749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84280, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84280, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84281 q = 1) (hb : d114750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84281, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84282 q = 1) (hb : d114751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84282, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84283 q = 1) (hb : d114752 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84283, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84284 q = 1) (hb : d114753 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84284, d114753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84284, d114753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32932 (p : Pattern) (ha : d84285 p = 1) (hb : d114754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32921 q ha hb
    | true =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28836 q ha hb
    | true =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d114697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84253 q = 1) (hb : d114718 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84253, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84253, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84285 q = 1) (hb : d114754 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84285, d114754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84285, d114754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32933 (p : Pattern) (ha : d84290 p = 1) (hb : d114759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32921 q ha hb
    | true =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28836 q ha hb
    | true =>
      simp only [d13298, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d114696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84259 q = 1) (hb : d114724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84259, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84259, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84260 q = 1) (hb : d114725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84260, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84260, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84290 q = 1) (hb : d114759 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84290, d114759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84290, d114759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32934 (p : Pattern) (ha : d84294 p = 1) (hb : d114763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84267 q = 1) (hb : d114736 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84267, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32928 q ha hb
    | true =>
      simp only [d84267, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84268 q = 1) (hb : d114737 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84268, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84268, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84229 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32921 q ha hb
    | true =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84230 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84269 q = 1) (hb : d114738 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84269, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84269, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84270 q = 1) (hb : d114739 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84270, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84270, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84271 q = 1) (hb : d114740 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84271, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84271, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84294 q = 1) (hb : d114763 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84294, d114763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84294, d114763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32935 (p : Pattern) (ha : d84297 p = 1) (hb : d114766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d114694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32921 q ha hb
    | true =>
      simp only [d84229, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d114695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84275 q = 1) (hb : d114744 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84275, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84275, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84276 q = 1) (hb : d114745 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84276, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84276, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84277 q = 1) (hb : d114746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84277, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84277, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84297 q = 1) (hb : d114766 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84297, d114766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84297, d114766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32936 (p : Pattern) (ha : d84303 p = 1) (hb : d114772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84255 q = 1) (hb : d114720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84255, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32926 q ha hb
    | true =>
      simp only [d84255, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28850 q hb ha
  have h2 (q : Pattern) (ha : d84256 q = 1) (hb : d114721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84256, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84256, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84257 q = 1) (hb : d114722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84257, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84257, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84258 q = 1) (hb : d114723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84258, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84258, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84262 q = 1) (hb : d114727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84262, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32927 q ha hb
    | true =>
      simp only [d84262, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28851 q hb ha
  have h6 (q : Pattern) (ha : d84263 q = 1) (hb : d114728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84263, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84263, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84264 q = 1) (hb : d114729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84264, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84264, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84273 q = 1) (hb : d114742 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84273, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32929 q ha hb
    | true =>
      simp only [d84273, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32922 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84274 q = 1) (hb : d114743 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84274, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84279 q = 1) (hb : d114748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84279, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32930 q ha hb
    | true =>
      simp only [d84279, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84280 q = 1) (hb : d114749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84280, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84280, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84281 q = 1) (hb : d114750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84281, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84282 q = 1) (hb : d114751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84282, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84283 q = 1) (hb : d114752 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84283, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84286 q = 1) (hb : d114755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84286, d114755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32932 q ha hb
    | true =>
      simp only [d84286, d114755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28861 q hb ha
  have h17 (q : Pattern) (ha : d84287 q = 1) (hb : d114756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84287, d114756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84287, d114756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84288 q = 1) (hb : d114757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84288, d114757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84288, d114757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84289 q = 1) (hb : d114758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84289, d114758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84289, d114758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84291 q = 1) (hb : d114760 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84291, d114760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32933 q ha hb
    | true =>
      simp only [d84291, d114760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28862 q hb ha
  have h21 (q : Pattern) (ha : d84292 q = 1) (hb : d114761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84292, d114761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84292, d114761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84293 q = 1) (hb : d114762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84293, d114762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84293, d114762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84295 q = 1) (hb : d114764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84295, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32934 q ha hb
    | true =>
      simp only [d84295, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32924 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84296 q = 1) (hb : d114765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84296, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84298 q = 1) (hb : d114767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84298, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32935 q ha hb
    | true =>
      simp only [d84298, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84299 q = 1) (hb : d114768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84299, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84299, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84300 q = 1) (hb : d114769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84300, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84301 q = 1) (hb : d114770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84301, d114770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84301, d114770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84302 q = 1) (hb : d114771 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84302, d114771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84302, d114771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84303 q = 1) (hb : d114772 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84303, d114772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84303, d114772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32937 (p : Pattern) (ha : d84305 p = 1) (hb : d114774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84235 q = 1) (hb : d114700 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32922 q ha hb
    | true =>
      simp only [d84235, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28837 q hb ha
  have h2 (q : Pattern) (ha : d84236 q = 1) (hb : d114701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84236, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84236, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84237 q = 1) (hb : d114702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84237, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84237, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84238 q = 1) (hb : d114703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84238, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84238, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84239 q = 1) (hb : d114704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84239, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84239, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13455 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28837 q ha hb
    | true =>
      simp only [d13455, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13456 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13457 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13457, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13458 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13459 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84305 q = 1) (hb : d114774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84305, d114774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84305, d114774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro32938 (p : Pattern) (ha : d84312 p = 1) (hb : d114781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84295 q = 1) (hb : d114764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84295, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32934 q ha hb
    | true =>
      simp only [d84295, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32924 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84296 q = 1) (hb : d114765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84296, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84298 q = 1) (hb : d114767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84298, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32935 q ha hb
    | true =>
      simp only [d84298, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84299 q = 1) (hb : d114768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84299, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84299, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84300 q = 1) (hb : d114769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84300, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84310 q = 1) (hb : d114779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84310, d114779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84310, d114779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84311 q = 1) (hb : d114780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84311, d114780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84311, d114780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84312 q = 1) (hb : d114781 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84312, d114781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84312, d114781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32939 (p : Pattern) (ha : d84319 p = 1) (hb : d114792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13483 q = 1) (hb : d53200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13483, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28872 q ha hb
    | true =>
      simp only [d13483, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22944 q ha hb
  have h2 (q : Pattern) (ha : d13484 q = 1) (hb : d53201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13484, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13484, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13485 q = 1) (hb : d53202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13485, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13485, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53205 q = 1) (hb : d114787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53205, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22944 q hb ha
    | true =>
      simp only [d53205, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53206 q = 1) (hb : d114788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53206, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53206, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53207 q = 1) (hb : d114789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53207, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53207, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53208 q = 1) (hb : d114790 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53208, d114790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53208, d114790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84318 q = 1) (hb : d114791 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84318, d114791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84318, d114791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84319 q = 1) (hb : d114792 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84319, d114792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84319, d114792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32940 (p : Pattern) (ha : d84323 p = 1) (hb : d114797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13500 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22944 q ha hb
    | true =>
      simp only [d13500, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10664 q ha hb
  have h2 (q : Pattern) (ha : d13501 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13502 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53214 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53215 q = 1) (hb : d88858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53215, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10664 q hb ha
    | true =>
      simp only [d53215, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53216 q = 1) (hb : d88859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53216, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53216, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53217 q = 1) (hb : d88860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53217, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53217, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53218 q = 1) (hb : d114795 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53218, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53218, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84322 q = 1) (hb : d114796 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84322, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84322, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84323 q = 1) (hb : d114797 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84323, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84323, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32941 (p : Pattern) (ha : d84329 p = 1) (hb : d114803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84320 q = 1) (hb : d114793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84320, d114793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32939 q ha hb
    | true =>
      simp only [d84320, d114793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84321 q = 1) (hb : d114794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84321, d114794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84321, d114794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84324 q = 1) (hb : d114798 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84324, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32940 q ha hb
    | true =>
      simp only [d84324, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84325 q = 1) (hb : d114799 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84325, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84325, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84326 q = 1) (hb : d114800 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84326, d114800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84326, d114800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84327 q = 1) (hb : d114801 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84327, d114801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84327, d114801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84328 q = 1) (hb : d114802 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84328, d114802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84328, d114802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84329 q = 1) (hb : d114803 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84329, d114803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84329, d114803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32942 (p : Pattern) (ha : d84333 p = 1) (hb : d114807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84324 q = 1) (hb : d114798 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84324, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32940 q ha hb
    | true =>
      simp only [d84324, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84325 q = 1) (hb : d114799 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84325, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84325, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28842 q ha hb
    | true =>
      simp only [d13523, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84330 q = 1) (hb : d114804 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84330, d114804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84330, d114804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84331 q = 1) (hb : d114805 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84331, d114805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84331, d114805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84332 q = 1) (hb : d114806 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84332, d114806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84332, d114806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84333 q = 1) (hb : d114807 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84333, d114807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84333, d114807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32943 (p : Pattern) (ha : d84340 p = 1) (hb : d114813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84324 q = 1) (hb : d114798 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84324, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32940 q ha hb
    | true =>
      simp only [d84324, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84325 q = 1) (hb : d114799 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84325, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84325, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84337 q = 1) (hb : d114810 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84337, d114810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84337, d114810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84338 q = 1) (hb : d114811 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84338, d114811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84338, d114811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84339 q = 1) (hb : d114812 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84339, d114812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84339, d114812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84340 q = 1) (hb : d114813 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84340, d114813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84340, d114813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32944 (p : Pattern) (ha : d84346 p = 1) (hb : d114819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84334 q = 1) (hb : d114808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84334, d114808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32941 q ha hb
    | true =>
      simp only [d84334, d114808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32942 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84335 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84336 q = 1) (hb : d114809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84336, d114809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84336, d114809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84341 q = 1) (hb : d114814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84341, d114814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32943 q ha hb
    | true =>
      simp only [d84341, d114814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84342 q = 1) (hb : d114815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84342, d114815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84342, d114815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84343 q = 1) (hb : d114816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84343, d114816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84343, d114816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84344 q = 1) (hb : d114817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84344, d114817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84344, d114817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84345 q = 1) (hb : d114818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84345, d114818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84345, d114818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84346 q = 1) (hb : d114819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84346, d114819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84346, d114819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32945 (p : Pattern) (ha : d84352 p = 1) (hb : d114825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84241 q = 1) (hb : d114706 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84241, d114706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84241, d114706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32923 q ha hb
  have h2 (q : Pattern) (ha : d84242 q = 1) (hb : d114707 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84242, d114707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84242, d114707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84250 q = 1) (hb : d114715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84250, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32923 q ha hb
    | true =>
      simp only [d84250, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32925 q ha hb
  have h4 (q : Pattern) (ha : d84251 q = 1) (hb : d114716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84251, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84251, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84252 q = 1) (hb : d114717 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84252, d114717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84252, d114717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84304 q = 1) (hb : d114773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84304, d114773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32931 q ha hb
    | true =>
      simp only [d84304, d114773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32936 q ha hb
  have h7 (q : Pattern) (ha : d84306 q = 1) (hb : d114775 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84306, d114775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32937 q ha hb
    | true =>
      simp only [d84306, d114775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28839 q hb ha
  have h8 (q : Pattern) (ha : d84307 q = 1) (hb : d114776 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84307, d114776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84307, d114776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84308 q = 1) (hb : d114777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84308, d114777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84308, d114777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84309 q = 1) (hb : d114778 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84309, d114778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84309, d114778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84313 q = 1) (hb : d114782 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84313, d114782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84313, d114782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32938 q ha hb
  have h12 (q : Pattern) (ha : d13476 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13476, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13476, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28840 q ha hb
  have h13 (q : Pattern) (ha : d84314 q = 1) (hb : d114783 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84314, d114783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84314, d114783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84315 q = 1) (hb : d114784 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84315, d114784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84315, d114784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84316 q = 1) (hb : d114785 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84316, d114785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84316, d114785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84317 q = 1) (hb : d114786 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84317, d114786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84317, d114786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84347 q = 1) (hb : d114820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84347, d114820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84347, d114820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32944 q ha hb
  have h18 (q : Pattern) (ha : d13593 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13593, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13593, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28844 q ha hb
  have h19 (q : Pattern) (ha : d84348 q = 1) (hb : d114821 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84348, d114821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84348, d114821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84349 q = 1) (hb : d114822 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84349, d114822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84349, d114822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84350 q = 1) (hb : d114823 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84350, d114823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84350, d114823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84351 q = 1) (hb : d114824 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84351, d114824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84351, d114824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84352 q = 1) (hb : d114825 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84352, d114825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84352, d114825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32946 (p : Pattern) (ha : d84358 p = 1) (hb : d114831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84353 q = 1) (hb : d114826 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84353, d114826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84353, d114826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32945 q ha hb
  have h2 (q : Pattern) (ha : d84354 q = 1) (hb : d114827 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84354, d114827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84354, d114827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84355 q = 1) (hb : d114828 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84355, d114828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84355, d114828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84356 q = 1) (hb : d114829 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84356, d114829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84356, d114829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84357 q = 1) (hb : d114830 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84357, d114830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84357, d114830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84358 q = 1) (hb : d114831 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84358, d114831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84358, d114831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32947 (p : Pattern) (ha : d84364 p = 1) (hb : d114838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13610 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22962 q ha hb
    | true =>
      simp only [d13610, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10677 q ha hb
  have h2 (q : Pattern) (ha : d13611 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13612 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53364 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53365 q = 1) (hb : d88948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53365, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10677 q hb ha
    | true =>
      simp only [d53365, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53366 q = 1) (hb : d88949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53366, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53366, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53367 q = 1) (hb : d88950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53367, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53367, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53368 q = 1) (hb : d114836 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53368, d114836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53368, d114836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84363 q = 1) (hb : d114837 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84363, d114837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84363, d114837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84364 q = 1) (hb : d114838 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84364, d114838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84364, d114838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32948 (p : Pattern) (ha : d84370 p = 1) (hb : d114844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32947 q ha hb
    | true =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28882 q ha hb
    | true =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d114841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d114842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84369 q = 1) (hb : d114843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84369, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84369, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84370 q = 1) (hb : d114844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84370, d114844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84370, d114844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32949 (p : Pattern) (ha : d84376 p = 1) (hb : d114850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84371 q = 1) (hb : d114845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32948 q ha hb
    | true =>
      simp only [d84371, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28883 q hb ha
  have h2 (q : Pattern) (ha : d84372 q = 1) (hb : d114846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84372, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84372, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84373 q = 1) (hb : d114847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84373, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84373, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84374 q = 1) (hb : d114848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84374, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84374, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84375 q = 1) (hb : d114849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84375, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84375, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84376 q = 1) (hb : d114850 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84376, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84376, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32950 (p : Pattern) (ha : d84379 p = 1) (hb : d114853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32947 q ha hb
    | true =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28882 q ha hb
    | true =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d114841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d114842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84369 q = 1) (hb : d114843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84369, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84369, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84379 q = 1) (hb : d114853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84379, d114853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84379, d114853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32951 (p : Pattern) (ha : d84385 p = 1) (hb : d114859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84371 q = 1) (hb : d114845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32948 q ha hb
    | true =>
      simp only [d84371, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28883 q hb ha
  have h2 (q : Pattern) (ha : d84372 q = 1) (hb : d114846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84372, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84372, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84373 q = 1) (hb : d114847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84373, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84373, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84374 q = 1) (hb : d114848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84374, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84374, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84375 q = 1) (hb : d114849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84375, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84375, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84380 q = 1) (hb : d114854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84380, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32950 q ha hb
    | true =>
      simp only [d84380, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28884 q hb ha
  have h7 (q : Pattern) (ha : d84381 q = 1) (hb : d114855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84381, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84381, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84382 q = 1) (hb : d114856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84382, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84382, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d84383 q = 1) (hb : d114857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84383, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84383, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84384 q = 1) (hb : d114858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84384, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84384, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84385 q = 1) (hb : d114859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84385, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84385, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32952 (p : Pattern) (ha : d84390 p = 1) (hb : d114864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32947 q ha hb
    | true =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28882 q ha hb
    | true =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d114841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d114842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84389 q = 1) (hb : d114863 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84389, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84389, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84390 q = 1) (hb : d114864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84390, d114864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84390, d114864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32953 (p : Pattern) (ha : d84397 p = 1) (hb : d114871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32947 q ha hb
    | true =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28882 q ha hb
    | true =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d114841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84395 q = 1) (hb : d114869 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84395, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84395, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84396 q = 1) (hb : d114870 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84396, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84396, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84397 q = 1) (hb : d114871 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84397, d114871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84397, d114871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32954 (p : Pattern) (ha : d84402 p = 1) (hb : d114880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13672 q = 1) (hb : d53429 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13672, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28901 q ha hb
    | true =>
      simp only [d13672, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22962 q ha hb
  have h2 (q : Pattern) (ha : d13673 q = 1) (hb : d53430 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13673, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13673, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13674 q = 1) (hb : d53431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13674, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13674, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53352 q = 1) (hb : d114875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53352, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22962 q hb ha
    | true =>
      simp only [d53352, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53353 q = 1) (hb : d114876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53353, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53353, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53354 q = 1) (hb : d114877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53354, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53354, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53432 q = 1) (hb : d114878 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53432, d114878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53432, d114878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84401 q = 1) (hb : d114879 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84401, d114879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84401, d114879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84402 q = 1) (hb : d114880 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84402, d114880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84402, d114880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32955 (p : Pattern) (ha : d84408 p = 1) (hb : d114886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84403 q = 1) (hb : d114881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84403, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32954 q ha hb
    | true =>
      simp only [d84403, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84404 q = 1) (hb : d114882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84404, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84404, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84365 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32947 q ha hb
    | true =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84366 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84405 q = 1) (hb : d114883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84405, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84405, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84406 q = 1) (hb : d114884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84406, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84406, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84407 q = 1) (hb : d114885 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84407, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84407, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84408 q = 1) (hb : d114886 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84408, d114886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84408, d114886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32956 (p : Pattern) (ha : d84414 p = 1) (hb : d114892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32947 q ha hb
    | true =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84411 q = 1) (hb : d114889 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84411, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84411, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84412 q = 1) (hb : d114890 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84412, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84412, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84413 q = 1) (hb : d114891 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84413, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84413, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84414 q = 1) (hb : d114892 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84414, d114892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84414, d114892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32957 (p : Pattern) (ha : d84420 p = 1) (hb : d114898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84391 q = 1) (hb : d114865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84391, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32952 q ha hb
    | true =>
      simp only [d84391, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28896 q hb ha
  have h2 (q : Pattern) (ha : d84392 q = 1) (hb : d114866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84392, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84392, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84393 q = 1) (hb : d114867 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84393, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84393, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84394 q = 1) (hb : d114868 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84394, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84394, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84398 q = 1) (hb : d114872 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84398, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32953 q ha hb
    | true =>
      simp only [d84398, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28897 q hb ha
  have h6 (q : Pattern) (ha : d84399 q = 1) (hb : d114873 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84399, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84399, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84400 q = 1) (hb : d114874 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84400, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84400, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84409 q = 1) (hb : d114887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84409, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32955 q ha hb
    | true =>
      simp only [d84409, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32948 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84410 q = 1) (hb : d114888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84410, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84415 q = 1) (hb : d114893 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84415, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32956 q ha hb
    | true =>
      simp only [d84415, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84416 q = 1) (hb : d114894 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84416, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84416, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84417 q = 1) (hb : d114895 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84417, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84418 q = 1) (hb : d114896 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84418, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84419 q = 1) (hb : d114897 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84419, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84420 q = 1) (hb : d114898 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84420, d114898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84420, d114898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32958 (p : Pattern) (ha : d84421 p = 1) (hb : d114899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32947 q ha hb
    | true =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28882 q ha hb
    | true =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d114841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d114842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84389 q = 1) (hb : d114863 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84389, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84389, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84421 q = 1) (hb : d114899 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84421, d114899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84421, d114899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32959 (p : Pattern) (ha : d84426 p = 1) (hb : d114904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32947 q ha hb
    | true =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28882 q ha hb
    | true =>
      simp only [d13625, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d114841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84395 q = 1) (hb : d114869 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84395, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84395, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84396 q = 1) (hb : d114870 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84396, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84396, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84426 q = 1) (hb : d114904 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84426, d114904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84426, d114904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32960 (p : Pattern) (ha : d84430 p = 1) (hb : d114908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84403 q = 1) (hb : d114881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84403, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32954 q ha hb
    | true =>
      simp only [d84403, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84404 q = 1) (hb : d114882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84404, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84404, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84365 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32947 q ha hb
    | true =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84366 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84405 q = 1) (hb : d114883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84405, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84405, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84406 q = 1) (hb : d114884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84406, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84406, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84407 q = 1) (hb : d114885 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84407, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84407, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84430 q = 1) (hb : d114908 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84430, d114908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84430, d114908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32961 (p : Pattern) (ha : d84433 p = 1) (hb : d114911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d114839 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32947 q ha hb
    | true =>
      simp only [d84365, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d114840 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84411 q = 1) (hb : d114889 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84411, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84411, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84412 q = 1) (hb : d114890 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84412, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84412, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84413 q = 1) (hb : d114891 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84413, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84413, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84433 q = 1) (hb : d114911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84433, d114911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84433, d114911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32962 (p : Pattern) (ha : d84439 p = 1) (hb : d114917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84391 q = 1) (hb : d114865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84391, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32952 q ha hb
    | true =>
      simp only [d84391, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28896 q hb ha
  have h2 (q : Pattern) (ha : d84392 q = 1) (hb : d114866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84392, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84392, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84393 q = 1) (hb : d114867 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84393, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84393, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84394 q = 1) (hb : d114868 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84394, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84394, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84398 q = 1) (hb : d114872 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84398, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32953 q ha hb
    | true =>
      simp only [d84398, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28897 q hb ha
  have h6 (q : Pattern) (ha : d84399 q = 1) (hb : d114873 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84399, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84399, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84400 q = 1) (hb : d114874 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84400, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84400, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84409 q = 1) (hb : d114887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84409, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32955 q ha hb
    | true =>
      simp only [d84409, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32948 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84410 q = 1) (hb : d114888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84410, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84415 q = 1) (hb : d114893 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84415, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32956 q ha hb
    | true =>
      simp only [d84415, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84416 q = 1) (hb : d114894 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84416, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84416, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84417 q = 1) (hb : d114895 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84417, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84418 q = 1) (hb : d114896 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84418, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84419 q = 1) (hb : d114897 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84419, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84422 q = 1) (hb : d114900 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84422, d114900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32958 q ha hb
    | true =>
      simp only [d84422, d114900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28907 q hb ha
  have h17 (q : Pattern) (ha : d84423 q = 1) (hb : d114901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84423, d114901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84423, d114901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84424 q = 1) (hb : d114902 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84424, d114902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84424, d114902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84425 q = 1) (hb : d114903 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84425, d114903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84425, d114903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84427 q = 1) (hb : d114905 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84427, d114905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32959 q ha hb
    | true =>
      simp only [d84427, d114905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28908 q hb ha
  have h21 (q : Pattern) (ha : d84428 q = 1) (hb : d114906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84428, d114906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84428, d114906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84429 q = 1) (hb : d114907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84429, d114907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84429, d114907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84431 q = 1) (hb : d114909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84431, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32960 q ha hb
    | true =>
      simp only [d84431, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32950 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84432 q = 1) (hb : d114910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84432, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84434 q = 1) (hb : d114912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84434, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32961 q ha hb
    | true =>
      simp only [d84434, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84435 q = 1) (hb : d114913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84435, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84435, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84436 q = 1) (hb : d114914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84436, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84437 q = 1) (hb : d114915 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84437, d114915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84437, d114915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84438 q = 1) (hb : d114916 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84438, d114916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84438, d114916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84439 q = 1) (hb : d114917 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84439, d114917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84439, d114917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32963 (p : Pattern) (ha : d84441 p = 1) (hb : d114919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84371 q = 1) (hb : d114845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32948 q ha hb
    | true =>
      simp only [d84371, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28883 q hb ha
  have h2 (q : Pattern) (ha : d84372 q = 1) (hb : d114846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84372, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84372, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84373 q = 1) (hb : d114847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84373, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84373, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84374 q = 1) (hb : d114848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84374, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84374, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84375 q = 1) (hb : d114849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84375, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84375, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13782 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28883 q ha hb
    | true =>
      simp only [d13782, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13783 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13784 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13784, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13785 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13786 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84441 q = 1) (hb : d114919 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84441, d114919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84441, d114919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro32964 (p : Pattern) (ha : d84448 p = 1) (hb : d114926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84431 q = 1) (hb : d114909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84431, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32960 q ha hb
    | true =>
      simp only [d84431, d114909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32950 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84432 q = 1) (hb : d114910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84432, d114910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84434 q = 1) (hb : d114912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84434, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32961 q ha hb
    | true =>
      simp only [d84434, d114912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84435 q = 1) (hb : d114913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84435, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84435, d114913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84436 q = 1) (hb : d114914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84436, d114914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84446 q = 1) (hb : d114924 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84446, d114924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84446, d114924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84447 q = 1) (hb : d114925 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84447, d114925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84447, d114925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84448 q = 1) (hb : d114926 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84448, d114926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84448, d114926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32965 (p : Pattern) (ha : d84455 p = 1) (hb : d114937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13810 q = 1) (hb : d53517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13810, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28918 q ha hb
    | true =>
      simp only [d13810, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22976 q ha hb
  have h2 (q : Pattern) (ha : d13811 q = 1) (hb : d53518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13811, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13811, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13812 q = 1) (hb : d53519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13812, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13812, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53522 q = 1) (hb : d114932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53522, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22976 q hb ha
    | true =>
      simp only [d53522, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53523 q = 1) (hb : d114933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53523, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53523, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53524 q = 1) (hb : d114934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53524, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53524, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53525 q = 1) (hb : d114935 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53525, d114935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53525, d114935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84454 q = 1) (hb : d114936 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84454, d114936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84454, d114936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84455 q = 1) (hb : d114937 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84455, d114937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84455, d114937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32966 (p : Pattern) (ha : d84459 p = 1) (hb : d114942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13827 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22976 q ha hb
    | true =>
      simp only [d13827, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10696 q ha hb
  have h2 (q : Pattern) (ha : d13828 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13829 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53531 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53532 q = 1) (hb : d89012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53532, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10696 q hb ha
    | true =>
      simp only [d53532, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53533 q = 1) (hb : d89013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53533, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53533, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53534 q = 1) (hb : d89014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53534, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53534, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53535 q = 1) (hb : d114940 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53535, d114940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53535, d114940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84458 q = 1) (hb : d114941 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84458, d114941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84458, d114941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84459 q = 1) (hb : d114942 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84459, d114942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84459, d114942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32967 (p : Pattern) (ha : d84465 p = 1) (hb : d114948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84456 q = 1) (hb : d114938 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84456, d114938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32965 q ha hb
    | true =>
      simp only [d84456, d114938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84457 q = 1) (hb : d114939 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84457, d114939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84457, d114939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84460 q = 1) (hb : d114943 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84460, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32966 q ha hb
    | true =>
      simp only [d84460, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84461 q = 1) (hb : d114944 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84461, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84461, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84462 q = 1) (hb : d114945 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84462, d114945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84462, d114945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84463 q = 1) (hb : d114946 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84463, d114946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84463, d114946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84464 q = 1) (hb : d114947 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84464, d114947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84464, d114947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84465 q = 1) (hb : d114948 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84465, d114948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84465, d114948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32968 (p : Pattern) (ha : d84469 p = 1) (hb : d114952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84460 q = 1) (hb : d114943 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84460, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32966 q ha hb
    | true =>
      simp only [d84460, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84461 q = 1) (hb : d114944 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84461, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84461, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28888 q ha hb
    | true =>
      simp only [d13850, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84466 q = 1) (hb : d114949 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84466, d114949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84466, d114949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84467 q = 1) (hb : d114950 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84467, d114950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84467, d114950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84468 q = 1) (hb : d114951 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84468, d114951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84468, d114951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84469 q = 1) (hb : d114952 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84469, d114952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84469, d114952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32969 (p : Pattern) (ha : d84476 p = 1) (hb : d114958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84460 q = 1) (hb : d114943 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84460, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32966 q ha hb
    | true =>
      simp only [d84460, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84461 q = 1) (hb : d114944 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84461, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84461, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84473 q = 1) (hb : d114955 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84473, d114955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84473, d114955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84474 q = 1) (hb : d114956 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84474, d114956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84474, d114956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84475 q = 1) (hb : d114957 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84475, d114957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84475, d114957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84476 q = 1) (hb : d114958 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84476, d114958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84476, d114958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32970 (p : Pattern) (ha : d84482 p = 1) (hb : d114964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84470 q = 1) (hb : d114953 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84470, d114953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32967 q ha hb
    | true =>
      simp only [d84470, d114953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32968 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84472 q = 1) (hb : d114954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84472, d114954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84472, d114954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84477 q = 1) (hb : d114959 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84477, d114959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32969 q ha hb
    | true =>
      simp only [d84477, d114959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84478 q = 1) (hb : d114960 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84478, d114960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84478, d114960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84479 q = 1) (hb : d114961 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84479, d114961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84479, d114961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84480 q = 1) (hb : d114962 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84480, d114962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84480, d114962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84481 q = 1) (hb : d114963 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84481, d114963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84481, d114963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84482 q = 1) (hb : d114964 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84482, d114964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84482, d114964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32971 (p : Pattern) (ha : d84488 p = 1) (hb : d114970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84377 q = 1) (hb : d114851 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84377, d114851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84377, d114851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32949 q ha hb
  have h2 (q : Pattern) (ha : d84378 q = 1) (hb : d114852 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84378, d114852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84378, d114852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84386 q = 1) (hb : d114860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84386, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32949 q ha hb
    | true =>
      simp only [d84386, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32951 q ha hb
  have h4 (q : Pattern) (ha : d84387 q = 1) (hb : d114861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84387, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84387, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84388 q = 1) (hb : d114862 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84388, d114862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84388, d114862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84440 q = 1) (hb : d114918 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84440, d114918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32957 q ha hb
    | true =>
      simp only [d84440, d114918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32962 q ha hb
  have h7 (q : Pattern) (ha : d84442 q = 1) (hb : d114920 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84442, d114920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32963 q ha hb
    | true =>
      simp only [d84442, d114920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28885 q hb ha
  have h8 (q : Pattern) (ha : d84443 q = 1) (hb : d114921 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84443, d114921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84443, d114921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84444 q = 1) (hb : d114922 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84444, d114922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84444, d114922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84445 q = 1) (hb : d114923 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84445, d114923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84445, d114923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84449 q = 1) (hb : d114927 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84449, d114927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84449, d114927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32964 q ha hb
  have h12 (q : Pattern) (ha : d13803 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13803, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13803, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28886 q ha hb
  have h13 (q : Pattern) (ha : d84450 q = 1) (hb : d114928 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84450, d114928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84450, d114928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84451 q = 1) (hb : d114929 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84451, d114929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84451, d114929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84452 q = 1) (hb : d114930 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84452, d114930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84452, d114930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84453 q = 1) (hb : d114931 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84453, d114931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84453, d114931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84483 q = 1) (hb : d114965 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84483, d114965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84483, d114965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32970 q ha hb
  have h18 (q : Pattern) (ha : d13920 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13920, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13920, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28890 q ha hb
  have h19 (q : Pattern) (ha : d84484 q = 1) (hb : d114966 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84484, d114966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84484, d114966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84485 q = 1) (hb : d114967 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84485, d114967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84485, d114967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84486 q = 1) (hb : d114968 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84486, d114968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84486, d114968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84487 q = 1) (hb : d114969 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84487, d114969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84487, d114969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84488 q = 1) (hb : d114970 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84488, d114970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84488, d114970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32972 (p : Pattern) (ha : d84494 p = 1) (hb : d114976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84489 q = 1) (hb : d114971 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84489, d114971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84489, d114971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32971 q ha hb
  have h2 (q : Pattern) (ha : d84490 q = 1) (hb : d114972 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84490, d114972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84490, d114972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84491 q = 1) (hb : d114973 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84491, d114973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84491, d114973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84492 q = 1) (hb : d114974 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84492, d114974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84492, d114974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84493 q = 1) (hb : d114975 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84493, d114975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84493, d114975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84494 q = 1) (hb : d114976 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84494, d114976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84494, d114976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32973 (p : Pattern) (ha : d84500 p = 1) (hb : d114982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d83957 q = 1) (hb : d114403 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83957, d114403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32844 q ha hb
    | true =>
      simp only [d83957, d114403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32868 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84090 q = 1) (hb : d114545 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84090, d114545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84090, d114545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32894 q ha hb
  have h3 (q : Pattern) (ha : d84091 q = 1) (hb : d114546 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84091, d114546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d84091, d114546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84224 q = 1) (hb : d114688 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84224, d114688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84224, d114688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32920 q ha hb
  have h5 (q : Pattern) (ha : d84225 q = 1) (hb : d114689 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84225, d114689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84225, d114689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84226 q = 1) (hb : d114690 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84226, d114690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84226, d114690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84359 q = 1) (hb : d114832 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84359, d114832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84359, d114832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32946 q ha hb
  have h8 (q : Pattern) (ha : d84360 q = 1) (hb : d114833 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84360, d114833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84360, d114833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84361 q = 1) (hb : d114834 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84361, d114834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84361, d114834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84362 q = 1) (hb : d114835 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84362, d114835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84362, d114835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84495 q = 1) (hb : d114977 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84495, d114977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84495, d114977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32972 q ha hb
  have h12 (q : Pattern) (ha : d84496 q = 1) (hb : d114978 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84496, d114978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84496, d114978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84497 q = 1) (hb : d114979 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84497, d114979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84497, d114979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84498 q = 1) (hb : d114980 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84498, d114980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84498, d114980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84499 q = 1) (hb : d114981 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d84499, d114981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84499, d114981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84500 q = 1) (hb : d114982 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d84500, d114982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84500, d114982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro32974 (p : Pattern) (ha : d84506 p = 1) (hb : d114988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84501 q = 1) (hb : d114983 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d84501, d114983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32973 q ha hb
    | true =>
      simp only [d84501, d114983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84502 q = 1) (hb : d114984 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d84502, d114984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84502, d114984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84503 q = 1) (hb : d114985 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d84503, d114985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84503, d114985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84504 q = 1) (hb : d114986 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d84504, d114986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84504, d114986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84505 q = 1) (hb : d114987 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d84505, d114987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84505, d114987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84506 q = 1) (hb : d114988 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d84506, d114988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84506, d114988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32975 (p : Pattern) (ha : d84512 p = 1) (hb : d114994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84507 q = 1) (hb : d114989 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d84507, d114989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32974 q ha hb
    | true =>
      simp only [d84507, d114989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84508 q = 1) (hb : d114990 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d84508, d114990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84508, d114990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84509 q = 1) (hb : d114991 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d84509, d114991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84509, d114991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84510 q = 1) (hb : d114992 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d84510, d114992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84510, d114992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84511 q = 1) (hb : d114993 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d84511, d114993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84511, d114993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84512 q = 1) (hb : d114994 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d84512, d114994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84512, d114994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32976 (p : Pattern) (ha : d84518 p = 1) (hb : d115000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84513 q = 1) (hb : d114995 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d84513, d114995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32975 q ha hb
    | true =>
      simp only [d84513, d114995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84514 q = 1) (hb : d114996 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d84514, d114996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84514, d114996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84515 q = 1) (hb : d114997 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d84515, d114997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84515, d114997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84516 q = 1) (hb : d114998 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d84516, d114998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84516, d114998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84517 q = 1) (hb : d114999 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d84517, d114999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84517, d114999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84518 q = 1) (hb : d115000 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d84518, d115000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84518, d115000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32977 (p : Pattern) (ha : d84524 p = 1) (hb : d115006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84519 q = 1) (hb : d115001 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d84519, d115001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32976 q ha hb
    | true =>
      simp only [d84519, d115001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84520 q = 1) (hb : d115002 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d84520, d115002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84520, d115002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84521 q = 1) (hb : d115003 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d84521, d115003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84521, d115003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84522 q = 1) (hb : d115004 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d84522, d115004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84522, d115004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84523 q = 1) (hb : d115005 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d84523, d115005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84523, d115005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84524 q = 1) (hb : d115006 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d84524, d115006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84524, d115006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32978 (p : Pattern) (ha : d84530 p = 1) (hb : d115012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84525 q = 1) (hb : d115007 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d84525, d115007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32977 q ha hb
    | true =>
      simp only [d84525, d115007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84526 q = 1) (hb : d115008 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d84526, d115008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84526, d115008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84527 q = 1) (hb : d115009 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d84527, d115009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84527, d115009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84528 q = 1) (hb : d115010 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d84528, d115010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84528, d115010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84529 q = 1) (hb : d115011 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d84529, d115011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84529, d115011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84530 q = 1) (hb : d115012 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d84530, d115012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84530, d115012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32979 (p : Pattern) (ha : d84536 p = 1) (hb : d115018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84531 q = 1) (hb : d115013 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d84531, d115013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32978 q ha hb
    | true =>
      simp only [d84531, d115013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84532 q = 1) (hb : d115014 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d84532, d115014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84532, d115014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84533 q = 1) (hb : d115015 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d84533, d115015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84533, d115015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84534 q = 1) (hb : d115016 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d84534, d115016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84534, d115016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84535 q = 1) (hb : d115017 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d84535, d115017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84535, d115017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84536 q = 1) (hb : d115018 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d84536, d115018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84536, d115018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32980 (p : Pattern) (ha : d84542 p = 1) (hb : d115024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84537 q = 1) (hb : d115019 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d84537, d115019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32979 q ha hb
    | true =>
      simp only [d84537, d115019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84538 q = 1) (hb : d115020 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d84538, d115020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84538, d115020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84539 q = 1) (hb : d115021 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d84539, d115021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84539, d115021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84540 q = 1) (hb : d115022 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d84540, d115022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84540, d115022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84541 q = 1) (hb : d115023 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d84541, d115023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84541, d115023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84542 q = 1) (hb : d115024 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d84542, d115024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84542, d115024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32981 (p : Pattern) (ha : d112688 p = 1) (hb : d150329 p = 1) : d115027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d112688 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12241 q = 1) (hb : d112688 q = 1) : d114115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32636 q ha hb
    | true =>
      simp only [d12241, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12292 q = 1) (hb : d112688 q = 1) : d114165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12293 q = 1) (hb : d112688 q = 1) : d114166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12293, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12294 q = 1) (hb : d112688 q = 1) : d114167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12295 q = 1) (hb : d112688 q = 1) : d114168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150329 q = 1) : d115027 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150329, d115027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150329, d115027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro32982 (p : Pattern) (ha : d112688 p = 1) (hb : d150339 p = 1) : d115037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d112688 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12268 q = 1) (hb : d112688 q = 1) : d114141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32640 q ha hb
    | true =>
      simp only [d12268, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150335 q = 1) : d115033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150335, d115033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150335, d115033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150336 q = 1) : d115034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150336, d115034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150336, d115034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150337 q = 1) : d115035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150337, d115035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150337, d115035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150338 q = 1) : d115036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150338, d115036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150338, d115036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150339 q = 1) : d115037 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150339, d115037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150339, d115037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32983 (p : Pattern) (ha : d112688 p = 1) (hb : d150345 p = 1) : d115043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d112688 q = 1) : d114170 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32643 q ha hb
    | true =>
      simp only [d12297, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32644 q ha hb
  have h2 (q : Pattern) (ha : d12298 q = 1) (hb : d112688 q = 1) : d114171 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150327 q = 1) : d115025 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150327, d115025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150327, d115025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150328 q = 1) : d115026 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150328, d115026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150328, d115026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150330 q = 1) : d115028 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150330, d115028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150330, d115028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32981 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150331 q = 1) : d115029 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150331, d115029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150331, d115029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150332 q = 1) : d115030 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150332, d115030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150332, d115030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d150333 q = 1) : d115031 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150333, d115031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150333, d115031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d150334 q = 1) : d115032 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150334, d115032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150334, d115032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d150340 q = 1) : d115038 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150340, d115038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150340, d115038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32982 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d150341 q = 1) : d115039 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150341, d115039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150341, d115039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d150342 q = 1) : d115040 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150342, d115040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150342, d115040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112688 q = 1) (hb : d150343 q = 1) : d115041 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150343, d115041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150343, d115041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d150344 q = 1) : d115042 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150344, d115042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150344, d115042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d150345 q = 1) : d115043 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150345, d115043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150345, d115043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32984 (p : Pattern) (ha : d112688 p = 1) (hb : d150351 p = 1) : d115049 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d112688 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150346 q = 1) : d115044 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150346, d115044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150346, d115044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32983 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150347 q = 1) : d115045 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150347, d115045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150347, d115045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150348 q = 1) : d115046 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150348, d115046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150348, d115046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150349 q = 1) : d115047 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150349, d115047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150349, d115047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150350 q = 1) : d115048 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150350, d115048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150350, d115048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150351 q = 1) : d115049 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150351, d115049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150351, d115049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32985 (p : Pattern) (ha : d112688 p = 1) (hb : d150354 p = 1) : d115052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12462 q = 1) (hb : d112688 q = 1) : d12462 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12463 q = 1) (hb : d112688 q = 1) : d114285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32667 q ha hb
    | true =>
      simp only [d12463, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12464 q = 1) (hb : d112688 q = 1) : d114286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12465 q = 1) (hb : d112688 q = 1) : d114287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12465, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12466 q = 1) (hb : d112688 q = 1) : d114288 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12467 q = 1) (hb : d112688 q = 1) : d114289 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150354 q = 1) : d115052 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150354, d115052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150354, d115052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro32986 (p : Pattern) (ha : d112688 p = 1) (hb : d150365 p = 1) : d115063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12668 q = 1) (hb : d112688 q = 1) : d12668 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150360 q = 1) : d115058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150360, d115058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32685 q hb ha
    | true =>
      simp only [d150360, d115058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150361 q = 1) : d115059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150361, d115059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150361, d115059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150362 q = 1) : d115060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150362, d115060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150362, d115060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150363 q = 1) : d115061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150363, d115061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150363, d115061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150364 q = 1) : d115062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150364, d115062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150364, d115062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150365 q = 1) : d115063 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150365, d115063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150365, d115063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32987 (p : Pattern) (ha : d112688 p = 1) (hb : d150371 p = 1) : d115069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12469 q = 1) (hb : d112688 q = 1) : d114291 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32666 q ha hb
    | true =>
      simp only [d12469, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32668 q ha hb
  have h2 (q : Pattern) (ha : d12470 q = 1) (hb : d112688 q = 1) : d114292 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12470, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150352 q = 1) : d115050 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150352, d115050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150352, d115050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150353 q = 1) : d115051 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150353, d115051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150353, d115051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150355 q = 1) : d115053 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150355, d115053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150355, d115053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32985 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150356 q = 1) : d115054 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150356, d115054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150356, d115054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150357 q = 1) : d115055 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150357, d115055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150357, d115055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d150358 q = 1) : d115056 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150358, d115056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150358, d115056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d150359 q = 1) : d115057 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150359, d115057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150359, d115057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d150366 q = 1) : d115064 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150366, d115064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150366, d115064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32986 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d150367 q = 1) : d115065 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150367, d115065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150367, d115065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d150368 q = 1) : d115066 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150368, d115066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150368, d115066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112688 q = 1) (hb : d150369 q = 1) : d115067 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150369, d115067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150369, d115067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d150370 q = 1) : d115068 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150370, d115068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150370, d115068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d150371 q = 1) : d115069 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150371, d115069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150371, d115069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32988 (p : Pattern) (ha : d112688 p = 1) (hb : d150377 p = 1) : d115075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150372 q = 1) : d115070 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150372, d115070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150372, d115070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32987 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150373 q = 1) : d115071 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150373, d115071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150373, d115071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150374 q = 1) : d115072 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150374, d115072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150374, d115072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150375 q = 1) : d115073 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150375, d115073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150375, d115073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150376 q = 1) : d115074 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150376, d115074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150376, d115074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150377 q = 1) : d115075 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150377, d115075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150377, d115075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32989 (p : Pattern) (ha : d112688 p = 1) (hb : d150381 p = 1) : d115079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12717 q = 1) (hb : d112688 q = 1) : d12717 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12718 q = 1) (hb : d112688 q = 1) : d114422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32693 q ha hb
    | true =>
      simp only [d12718, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12719 q = 1) (hb : d112688 q = 1) : d114423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12720 q = 1) (hb : d112688 q = 1) : d114424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12720, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12721 q = 1) (hb : d112688 q = 1) : d114425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12722 q = 1) (hb : d112688 q = 1) : d114426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150381 q = 1) : d115079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150381, d115079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150381, d115079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro32990 (p : Pattern) (ha : d112688 p = 1) (hb : d150392 p = 1) : d115090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12935 q = 1) (hb : d112688 q = 1) : d12935 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150387 q = 1) : d115085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150387, d115085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32711 q hb ha
    | true =>
      simp only [d150387, d115085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150388 q = 1) : d115086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150388, d115086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150388, d115086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150389 q = 1) : d115087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150389, d115087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150389, d115087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150390 q = 1) : d115088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150390, d115088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150390, d115088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150391 q = 1) : d115089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150391, d115089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150391, d115089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150392 q = 1) : d115090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150392, d115090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150392, d115090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32991 (p : Pattern) (ha : d112688 p = 1) (hb : d150398 p = 1) : d115096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12724 q = 1) (hb : d112688 q = 1) : d114428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32692 q ha hb
    | true =>
      simp only [d12724, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32694 q ha hb
  have h2 (q : Pattern) (ha : d12725 q = 1) (hb : d112688 q = 1) : d114429 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12725, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150379 q = 1) : d115077 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150379, d115077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150379, d115077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150380 q = 1) : d115078 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150380, d115078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150380, d115078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150382 q = 1) : d115080 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150382, d115080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150382, d115080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32989 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150383 q = 1) : d115081 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150383, d115081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150383, d115081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150384 q = 1) : d115082 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150384, d115082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150384, d115082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d150385 q = 1) : d115083 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150385, d115083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150385, d115083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d150386 q = 1) : d115084 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150386, d115084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150386, d115084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d150393 q = 1) : d115091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150393, d115091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150393, d115091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32990 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d150394 q = 1) : d115092 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150394, d115092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150394, d115092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d150395 q = 1) : d115093 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150395, d115093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150395, d115093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112688 q = 1) (hb : d150396 q = 1) : d115094 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150396, d115094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150396, d115094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d150397 q = 1) : d115095 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150397, d115095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150397, d115095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d150398 q = 1) : d115096 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150398, d115096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150398, d115096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32992 (p : Pattern) (ha : d112688 p = 1) (hb : d150404 p = 1) : d115102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150399 q = 1) : d115097 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150399, d115097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150399, d115097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32991 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150400 q = 1) : d115098 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150400, d115098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150400, d115098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150401 q = 1) : d115099 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150401, d115099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150401, d115099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150402 q = 1) : d115100 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150402, d115100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150402, d115100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150403 q = 1) : d115101 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150403, d115101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150403, d115101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150404 q = 1) : d115102 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150404, d115102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150404, d115102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32993 (p : Pattern) (ha : d112688 p = 1) (hb : d150409 p = 1) : d115107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12991 q = 1) (hb : d112688 q = 1) : d12991 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12992 q = 1) (hb : d112688 q = 1) : d114565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32719 q ha hb
    | true =>
      simp only [d12992, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12993 q = 1) (hb : d112688 q = 1) : d114566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12994 q = 1) (hb : d112688 q = 1) : d114567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12994, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12995 q = 1) (hb : d112688 q = 1) : d114568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12996 q = 1) (hb : d112688 q = 1) : d114569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150409 q = 1) : d115107 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150409, d115107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150409, d115107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro32994 (p : Pattern) (ha : d112688 p = 1) (hb : d150418 p = 1) : d114663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d112688 q = 1) : d114654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32741 q ha hb
    | true =>
      simp only [d13244, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d112688 q = 1) : d114655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13198 q = 1) (hb : d112688 q = 1) : d13198 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150415 q = 1) : d114660 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150415, d114660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150415, d114660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150416 q = 1) : d114661 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150416, d114661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150416, d114661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150417 q = 1) : d114662 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150417, d114662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150417, d114662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150418 q = 1) : d114663 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150418, d114663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150418, d114663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro32995 (p : Pattern) (ha : d112688 p = 1) (hb : d150424 p = 1) : d115118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13260 q = 1) (hb : d112688 q = 1) : d13260 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150419 q = 1) : d115113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150419, d115113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32994 q ha hb
    | true =>
      simp only [d150419, d115113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150420 q = 1) : d115114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150420, d115114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150420, d115114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150421 q = 1) : d115115 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150421, d115115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150421, d115115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150422 q = 1) : d115116 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150422, d115116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150422, d115116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150423 q = 1) : d115117 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150423, d115117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150423, d115117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150424 q = 1) : d115118 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150424, d115118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150424, d115118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32996 (p : Pattern) (ha : d112688 p = 1) (hb : d150430 p = 1) : d115124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12998 q = 1) (hb : d112688 q = 1) : d114571 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32718 q ha hb
    | true =>
      simp only [d12998, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32720 q ha hb
  have h2 (q : Pattern) (ha : d12999 q = 1) (hb : d112688 q = 1) : d114572 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12999, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150407 q = 1) : d115105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150407, d115105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150407, d115105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150408 q = 1) : d115106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150408, d115106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150408, d115106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150410 q = 1) : d115108 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150410, d115108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150410, d115108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32993 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150411 q = 1) : d115109 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150411, d115109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150411, d115109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150412 q = 1) : d115110 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150412, d115110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150412, d115110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d150413 q = 1) : d115111 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150413, d115111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150413, d115111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d150414 q = 1) : d115112 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150414, d115112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150414, d115112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d150425 q = 1) : d115119 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150425, d115119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150425, d115119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32995 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d150426 q = 1) : d115120 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150426, d115120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150426, d115120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d150427 q = 1) : d115121 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150427, d115121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150427, d115121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112688 q = 1) (hb : d150428 q = 1) : d115122 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150428, d115122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150428, d115122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d150429 q = 1) : d115123 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150429, d115123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150429, d115123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d150430 q = 1) : d115124 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150430, d115124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150430, d115124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32997 (p : Pattern) (ha : d112688 p = 1) (hb : d150436 p = 1) : d115130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150431 q = 1) : d115125 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150431, d115125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150431, d115125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32996 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150432 q = 1) : d115126 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150432, d115126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150432, d115126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150433 q = 1) : d115127 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150433, d115127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150433, d115127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150434 q = 1) : d115128 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150434, d115128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150434, d115128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150435 q = 1) : d115129 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150435, d115129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150435, d115129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150436 q = 1) : d115130 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150436, d115130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150436, d115130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32998 (p : Pattern) (ha : d112688 p = 1) (hb : d150442 p = 1) : d115136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13317 q = 1) (hb : d112688 q = 1) : d13317 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13318 q = 1) (hb : d112688 q = 1) : d114709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32749 q ha hb
    | true =>
      simp only [d13318, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13319 q = 1) (hb : d112688 q = 1) : d114710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13320 q = 1) (hb : d112688 q = 1) : d114711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13320, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13321 q = 1) (hb : d112688 q = 1) : d114712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13322 q = 1) (hb : d112688 q = 1) : d114713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150442 q = 1) : d115136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150442, d115136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150442, d115136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro32999 (p : Pattern) (ha : d112688 p = 1) (hb : d150451 p = 1) : d114807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d112688 q = 1) : d114798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32771 q ha hb
    | true =>
      simp only [d13570, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d112688 q = 1) : d114799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13524 q = 1) (hb : d112688 q = 1) : d13524 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150448 q = 1) : d114804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150448, d114804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150448, d114804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150449 q = 1) : d114805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150449, d114805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150449, d114805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150450 q = 1) : d114806 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150450, d114806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150450, d114806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150451 q = 1) : d114807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150451, d114807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150451, d114807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
end NetHack.Soko22Hazard87
