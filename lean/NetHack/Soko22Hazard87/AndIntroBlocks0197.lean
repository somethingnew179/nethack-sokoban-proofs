import NetHack.Soko22Hazard87.AndIntroBlocks0196
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro49250 (p : Pattern) (ha : d21787 p = 1) (hb : d169395 p = 1) : d170028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21777 q = 1) (hb : d169395 q = 1) : d21777 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21778 q = 1) (hb : d169395 q = 1) : d170019 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
    | true =>
      simp only [d21778, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21779 q = 1) (hb : d169395 q = 1) : d170020 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21780 q = 1) (hb : d169395 q = 1) : d170021 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21781 q = 1) (hb : d169395 q = 1) : d170022 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21781, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21786 q = 1) (hb : d169395 q = 1) : d170027 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21786, d170027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21786, d170027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21787 q = 1) (hb : d169395 q = 1) : d170028 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21787, d170028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21787, d170028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49251 (p : Pattern) (ha : d21793 p = 1) (hb : d169395 p = 1) : d170034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d169395 q = 1) : d170025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49249 q ha hb
    | true =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d169395 q = 1) : d170026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d169395 q = 1) : d170031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d169395 q = 1) : d170032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d169395 q = 1) : d170033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21793 q = 1) (hb : d169395 q = 1) : d170034 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21793, d170034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21793, d170034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49252 (p : Pattern) (ha : d21797 p = 1) (hb : d169395 p = 1) : d170038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d169395 q = 1) : d170035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d169395 q = 1) : d170036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d169395 q = 1) : d170037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21797 q = 1) (hb : d169395 q = 1) : d170038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21797, d170038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21797, d170038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49253 (p : Pattern) (ha : d21803 p = 1) (hb : d169395 p = 1) : d170044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d169395 q = 1) : d170039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49251 q ha hb
    | true =>
      simp only [d21798, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49252 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d169395 q = 1) : d170040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d169395 q = 1) : d170041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d169395 q = 1) : d170042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d169395 q = 1) : d170043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21803 q = 1) (hb : d169395 q = 1) : d170044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21803, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21803, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49254 (p : Pattern) (ha : d21806 p = 1) (hb : d169395 p = 1) : d170047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d169395 q = 1) : d170025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49249 q ha hb
    | true =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d169395 q = 1) : d170026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d169395 q = 1) : d170031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d169395 q = 1) : d170032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d169395 q = 1) : d170033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21806 q = 1) (hb : d169395 q = 1) : d170047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21806, d170047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21806, d170047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49255 (p : Pattern) (ha : d21807 p = 1) (hb : d169395 p = 1) : d170048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d169395 q = 1) : d170035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d169395 q = 1) : d170036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d169395 q = 1) : d170037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21807 q = 1) (hb : d169395 q = 1) : d170048 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21807, d170048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21807, d170048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49256 (p : Pattern) (ha : d21813 p = 1) (hb : d169395 p = 1) : d170054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d169395 q = 1) : d170039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49251 q ha hb
    | true =>
      simp only [d21798, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49252 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d169395 q = 1) : d170040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d169395 q = 1) : d170041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d169395 q = 1) : d170042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d169395 q = 1) : d170043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21808 q = 1) (hb : d169395 q = 1) : d170049 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49254 q ha hb
    | true =>
      simp only [d21808, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49255 q ha hb
  have h7 (q : Pattern) (ha : d21809 q = 1) (hb : d169395 q = 1) : d170050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21810 q = 1) (hb : d169395 q = 1) : d170051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21810, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21811 q = 1) (hb : d169395 q = 1) : d170052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21812 q = 1) (hb : d169395 q = 1) : d170053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21813 q = 1) (hb : d169395 q = 1) : d170054 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21813, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21813, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49257 (p : Pattern) (ha : d21867 p = 1) (hb : d169395 p = 1) : d170093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d169395 q = 1) : d170012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49247 q ha hb
    | true =>
      simp only [d21762, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d169395 q = 1) : d170013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d169395 q = 1) : d170014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21771 q = 1) (hb : d169395 q = 1) : d21771 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21772 q = 1) (hb : d169395 q = 1) : d170015 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
    | true =>
      simp only [d21772, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21773 q = 1) (hb : d169395 q = 1) : d170016 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21774 q = 1) (hb : d169395 q = 1) : d170017 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21775 q = 1) (hb : d169395 q = 1) : d170018 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21865 q = 1) (hb : d169395 q = 1) : d170091 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21865, d170091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21865, d170091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21866 q = 1) (hb : d169395 q = 1) : d170092 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21866, d170092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21866, d170092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21867 q = 1) (hb : d169395 q = 1) : d170093 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21867, d170093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21867, d170093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro49258 (p : Pattern) (ha : d21877 p = 1) (hb : d169395 p = 1) : d170103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21868 q = 1) (hb : d169395 q = 1) : d170094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49257 q ha hb
    | true =>
      simp only [d21868, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21869 q = 1) (hb : d169395 q = 1) : d170095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21874 q = 1) (hb : d169395 q = 1) : d170100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21874, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21874, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21875 q = 1) (hb : d169395 q = 1) : d170101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21875, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21875, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21876 q = 1) (hb : d169395 q = 1) : d170102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21876, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21876, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21877 q = 1) (hb : d169395 q = 1) : d170103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21877, d170103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21877, d170103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49259 (p : Pattern) (ha : d22003 p = 1) (hb : d169395 p = 1) : d170157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21993 q = 1) (hb : d169395 q = 1) : d170147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21993, d170147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49258 q ha hb
    | true =>
      simp only [d21993, d170147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49252 q ha hb
  have h2 (q : Pattern) (ha : d21994 q = 1) (hb : d169395 q = 1) : d170148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21994, d170148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21994, d170148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21995 q = 1) (hb : d169395 q = 1) : d170149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21995, d170149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21995, d170149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21996 q = 1) (hb : d169395 q = 1) : d170150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21996, d170150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21996, d170150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21997 q = 1) (hb : d169395 q = 1) : d170151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21997, d170151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21997, d170151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21998 q = 1) (hb : d169395 q = 1) : d170152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21998, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49252 q ha hb
    | true =>
      simp only [d21998, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21999 q = 1) (hb : d169395 q = 1) : d170153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21999, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21999, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22000 q = 1) (hb : d169395 q = 1) : d170154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22000, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22000, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22001 q = 1) (hb : d169395 q = 1) : d170155 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22001, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22001, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22002 q = 1) (hb : d169395 q = 1) : d170156 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22002, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22002, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22003 q = 1) (hb : d169395 q = 1) : d170157 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22003, d170157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22003, d170157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49260 (p : Pattern) (ha : d22009 p = 1) (hb : d169395 p = 1) : d170163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21998 q = 1) (hb : d169395 q = 1) : d170152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21998, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49252 q ha hb
    | true =>
      simp only [d21998, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21999 q = 1) (hb : d169395 q = 1) : d170153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21999, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21999, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22000 q = 1) (hb : d169395 q = 1) : d170154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22000, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22000, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22001 q = 1) (hb : d169395 q = 1) : d170155 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22001, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22001, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22002 q = 1) (hb : d169395 q = 1) : d170156 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22002, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22002, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22004 q = 1) (hb : d169395 q = 1) : d170158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22004, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49255 q ha hb
    | true =>
      simp only [d22004, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22005 q = 1) (hb : d169395 q = 1) : d170159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22005, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22005, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22006 q = 1) (hb : d169395 q = 1) : d170160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22006, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22006, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22007 q = 1) (hb : d169395 q = 1) : d170161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22007, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22007, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22008 q = 1) (hb : d169395 q = 1) : d170162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22008, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22008, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22009 q = 1) (hb : d169395 q = 1) : d170163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22009, d170163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22009, d170163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49261 (p : Pattern) (ha : d22018 p = 1) (hb : d169395 p = 1) : d170172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22004 q = 1) (hb : d169395 q = 1) : d170158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22004, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49255 q ha hb
    | true =>
      simp only [d22004, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22005 q = 1) (hb : d169395 q = 1) : d170159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22005, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22005, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22006 q = 1) (hb : d169395 q = 1) : d170160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22006, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22006, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22007 q = 1) (hb : d169395 q = 1) : d170161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22007, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22007, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22008 q = 1) (hb : d169395 q = 1) : d170162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22008, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22008, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22018 q = 1) (hb : d169395 q = 1) : d170172 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22018, d170172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22018, d170172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49262 (p : Pattern) (ha : d22069 p = 1) (hb : d169395 p = 1) : d170194 p = 1 := by
  have h0 (q : Pattern) (ha : d22046 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22067 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22068 q = 1) (hb : d169395 q = 1) : d170193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22068, d169395, d170193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22068, d169395, d170193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22058 q = 1) (hb : d169395 q = 1) : d22058 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22069 q = 1) (hb : d169395 q = 1) : d170194 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22069, d170194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22069, d170194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49263 (p : Pattern) (ha : d22103 p = 1) (hb : d169395 p = 1) : d170220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22097 q = 1) (hb : d169395 q = 1) : d22097 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22098 q = 1) (hb : d169395 q = 1) : d170215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
    | true =>
      simp only [d22098, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22099 q = 1) (hb : d169395 q = 1) : d170216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22100 q = 1) (hb : d169395 q = 1) : d170217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22101 q = 1) (hb : d169395 q = 1) : d170218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22101, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22102 q = 1) (hb : d169395 q = 1) : d170219 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22102, d170219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22102, d170219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22103 q = 1) (hb : d169395 q = 1) : d170220 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22103, d170220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22103, d170220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49264 (p : Pattern) (ha : d22197 p = 1) (hb : d169395 p = 1) : d170251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22104 q = 1) (hb : d169395 q = 1) : d170221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49263 q ha hb
    | true =>
      simp only [d22104, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22105 q = 1) (hb : d169395 q = 1) : d170222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22194 q = 1) (hb : d169395 q = 1) : d170248 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22194, d170248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22194, d170248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22195 q = 1) (hb : d169395 q = 1) : d170249 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22195, d170249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22195, d170249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22196 q = 1) (hb : d169395 q = 1) : d170250 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22196, d170250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22196, d170250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22197 q = 1) (hb : d169395 q = 1) : d170251 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22197, d170251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22197, d170251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49265 (p : Pattern) (ha : d22203 p = 1) (hb : d169395 p = 1) : d170257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22198 q = 1) (hb : d169395 q = 1) : d170252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22198, d170252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49264 q ha hb
    | true =>
      simp only [d22198, d170252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22199 q = 1) (hb : d169395 q = 1) : d170253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22199, d170253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22199, d170253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22200 q = 1) (hb : d169395 q = 1) : d170254 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22200, d170254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22200, d170254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22201 q = 1) (hb : d169395 q = 1) : d170255 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22201, d170255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22201, d170255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22202 q = 1) (hb : d169395 q = 1) : d170256 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22202, d170256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22202, d170256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22203 q = 1) (hb : d169395 q = 1) : d170257 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22203, d170257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22203, d170257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49266 (p : Pattern) (ha : d21818 p = 1) (hb : d169395 p = 1) : d170059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d169395 q = 1) : d170025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49249 q ha hb
    | true =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d169395 q = 1) : d170026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d169395 q = 1) : d170031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d169395 q = 1) : d170032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21817 q = 1) (hb : d169395 q = 1) : d170058 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21817, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21817, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21818 q = 1) (hb : d169395 q = 1) : d170059 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21818, d170059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21818, d170059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49267 (p : Pattern) (ha : d21820 p = 1) (hb : d169395 p = 1) : d170061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d169395 q = 1) : d170035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d169395 q = 1) : d170036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21819 q = 1) (hb : d169395 q = 1) : d170060 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21819, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21819, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21820 q = 1) (hb : d169395 q = 1) : d170061 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21820, d170061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21820, d170061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49268 (p : Pattern) (ha : d21827 p = 1) (hb : d169395 p = 1) : d170068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d169395 q = 1) : d170025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49249 q ha hb
    | true =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d169395 q = 1) : d170026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d169395 q = 1) : d170031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21825 q = 1) (hb : d169395 q = 1) : d170066 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21825, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21825, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21826 q = 1) (hb : d169395 q = 1) : d170067 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21826, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21826, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21827 q = 1) (hb : d169395 q = 1) : d170068 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21827, d170068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21827, d170068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49269 (p : Pattern) (ha : d21830 p = 1) (hb : d169395 p = 1) : d170071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d169395 q = 1) : d170035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21828 q = 1) (hb : d169395 q = 1) : d170069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21828, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21828, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21829 q = 1) (hb : d169395 q = 1) : d170070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21829, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21829, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21830 q = 1) (hb : d169395 q = 1) : d170071 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21830, d170071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21830, d170071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49270 (p : Pattern) (ha : d21846 p = 1) (hb : d169395 p = 1) : d170077 p = 1 := by
  have h0 (q : Pattern) (ha : d21838 q = 1) (hb : d116750 q = 1) : d21838 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21740 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21839 q = 1) (hb : d169395 q = 1) : d170075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21839, d169395, d170075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21839, d169395, d170075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21844 q = 1) (hb : d116750 q = 1) : d21844 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21845 q = 1) (hb : d169395 q = 1) : d170076 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21845, d169395, d170076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21845, d169395, d170076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21846 q = 1) (hb : d169395 q = 1) : d170077 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21846, d170077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21846, d170077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49271 (p : Pattern) (ha : d21856 p = 1) (hb : d169395 p = 1) : d170082 p = 1 := by
  have h0 (q : Pattern) (ha : d21854 q = 1) (hb : d116750 q = 1) : d21854 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13028 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21855 q = 1) (hb : d169395 q = 1) : d170081 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21855, d169395, d170081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21855, d169395, d170081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21760 q = 1) (hb : d169395 q = 1) : d21760 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21856 q = 1) (hb : d169395 q = 1) : d170082 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21856, d170082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21856, d170082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49272 (p : Pattern) (ha : d21862 p = 1) (hb : d169395 p = 1) : d170088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21847 q = 1) (hb : d169395 q = 1) : d170078 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21847, d170078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49270 q ha hb
    | true =>
      simp only [d21847, d170078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49247 q ha hb
  have h2 (q : Pattern) (ha : d21848 q = 1) (hb : d169395 q = 1) : d170079 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21848, d170079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21848, d170079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21849 q = 1) (hb : d169395 q = 1) : d170080 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21849, d170080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21849, d170080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21857 q = 1) (hb : d169395 q = 1) : d170083 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21857, d170083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49247 q ha hb
    | true =>
      simp only [d21857, d170083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49271 q ha hb
  have h5 (q : Pattern) (ha : d21858 q = 1) (hb : d169395 q = 1) : d170084 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21858, d170084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21858, d170084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21859 q = 1) (hb : d169395 q = 1) : d170085 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21859, d170085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21859, d170085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21860 q = 1) (hb : d169395 q = 1) : d170086 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21860, d170086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21860, d170086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21762 q = 1) (hb : d169395 q = 1) : d170012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49247 q ha hb
    | true =>
      simp only [d21762, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
  have h9 (q : Pattern) (ha : d21763 q = 1) (hb : d169395 q = 1) : d170013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21764 q = 1) (hb : d169395 q = 1) : d170014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21771 q = 1) (hb : d169395 q = 1) : d21771 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d21772 q = 1) (hb : d169395 q = 1) : d170015 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
    | true =>
      simp only [d21772, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21773 q = 1) (hb : d169395 q = 1) : d170016 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21774 q = 1) (hb : d169395 q = 1) : d170017 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21775 q = 1) (hb : d169395 q = 1) : d170018 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21775, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21861 q = 1) (hb : d169395 q = 1) : d170087 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21861, d170087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21861, d170087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21862 q = 1) (hb : d169395 q = 1) : d170088 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21862, d170088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21862, d170088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro49273 (p : Pattern) (ha : d21873 p = 1) (hb : d169395 p = 1) : d170099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21863 q = 1) (hb : d169395 q = 1) : d170089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21863, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49272 q ha hb
    | true =>
      simp only [d21863, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21864 q = 1) (hb : d169395 q = 1) : d170090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21864, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21864, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21868 q = 1) (hb : d169395 q = 1) : d170094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49257 q ha hb
    | true =>
      simp only [d21868, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21869 q = 1) (hb : d169395 q = 1) : d170095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21870 q = 1) (hb : d169395 q = 1) : d170096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21870, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21870, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21871 q = 1) (hb : d169395 q = 1) : d170097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21871, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21871, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21872 q = 1) (hb : d169395 q = 1) : d170098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21872, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21872, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21873 q = 1) (hb : d169395 q = 1) : d170099 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21873, d170099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21873, d170099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49274 (p : Pattern) (ha : d21954 p = 1) (hb : d169395 p = 1) : d170111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d169395 q = 1) : d170012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49247 q ha hb
    | true =>
      simp only [d21762, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d169395 q = 1) : d170013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d169395 q = 1) : d170014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21771 q = 1) (hb : d169395 q = 1) : d21771 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21772 q = 1) (hb : d169395 q = 1) : d170015 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
    | true =>
      simp only [d21772, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21773 q = 1) (hb : d169395 q = 1) : d170016 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21774 q = 1) (hb : d169395 q = 1) : d170017 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21775 q = 1) (hb : d169395 q = 1) : d170018 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21948 q = 1) (hb : d169395 q = 1) : d21948 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21949 q = 1) (hb : d169395 q = 1) : d170106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21949, d170106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
    | true =>
      simp only [d21949, d170106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21950 q = 1) (hb : d169395 q = 1) : d170107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21950, d170107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21950, d170107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21951 q = 1) (hb : d169395 q = 1) : d170108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21951, d170108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21951, d170108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21952 q = 1) (hb : d169395 q = 1) : d170109 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21952, d170109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21952, d170109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d21953 q = 1) (hb : d169395 q = 1) : d170110 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21953, d170110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21953, d170110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21954 q = 1) (hb : d169395 q = 1) : d170111 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21954, d170111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21954, d170111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro49275 (p : Pattern) (ha : d21960 p = 1) (hb : d169395 p = 1) : d170117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21955 q = 1) (hb : d169395 q = 1) : d170112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21955, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49274 q ha hb
    | true =>
      simp only [d21955, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21956 q = 1) (hb : d169395 q = 1) : d170113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21956, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21956, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21957 q = 1) (hb : d169395 q = 1) : d170114 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21957, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21957, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21958 q = 1) (hb : d169395 q = 1) : d170115 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21958, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21958, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21959 q = 1) (hb : d169395 q = 1) : d170116 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21959, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21959, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21960 q = 1) (hb : d169395 q = 1) : d170117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21960, d170117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21960, d170117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49276 (p : Pattern) (ha : d150159 p = 1) (hb : d169395 p = 1) : d170123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21821 q = 1) (hb : d169395 q = 1) : d170062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21821, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49266 q ha hb
    | true =>
      simp only [d21821, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49267 q ha hb
  have h2 (q : Pattern) (ha : d21822 q = 1) (hb : d169395 q = 1) : d170063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21822, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21822, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21823 q = 1) (hb : d169395 q = 1) : d170064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21823, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21823, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21824 q = 1) (hb : d169395 q = 1) : d170065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21824, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21824, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21831 q = 1) (hb : d169395 q = 1) : d170072 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21831, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49268 q ha hb
    | true =>
      simp only [d21831, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49269 q ha hb
  have h6 (q : Pattern) (ha : d21832 q = 1) (hb : d169395 q = 1) : d170073 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21832, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21832, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21833 q = 1) (hb : d169395 q = 1) : d170074 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21833, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21833, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21878 q = 1) (hb : d169395 q = 1) : d170104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21878, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49273 q ha hb
    | true =>
      simp only [d21878, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49258 q ha hb
  have h9 (q : Pattern) (ha : d150155 q = 1) (hb : d169395 q = 1) : d170105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150155, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21961 q = 1) (hb : d169395 q = 1) : d170118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21961, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49275 q ha hb
    | true =>
      simp only [d21961, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21962 q = 1) (hb : d169395 q = 1) : d170119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21962, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21962, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150156 q = 1) (hb : d169395 q = 1) : d170120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150156, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150157 q = 1) (hb : d169395 q = 1) : d170121 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150157, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150158 q = 1) (hb : d169395 q = 1) : d170122 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150158, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150159 q = 1) (hb : d169395 q = 1) : d170123 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150159, d170123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150159, d170123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49277 (p : Pattern) (ha : d21967 p = 1) (hb : d169395 p = 1) : d170124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d169395 q = 1) : d170025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49249 q ha hb
    | true =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d169395 q = 1) : d170026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d169395 q = 1) : d170031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d169395 q = 1) : d170032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21817 q = 1) (hb : d169395 q = 1) : d170058 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21817, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21817, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21967 q = 1) (hb : d169395 q = 1) : d170124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21967, d170124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21967, d170124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49278 (p : Pattern) (ha : d21968 p = 1) (hb : d169395 p = 1) : d170125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d169395 q = 1) : d170035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d169395 q = 1) : d170036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21819 q = 1) (hb : d169395 q = 1) : d170060 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21819, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21819, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21968 q = 1) (hb : d169395 q = 1) : d170125 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21968, d170125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21968, d170125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49279 (p : Pattern) (ha : d21973 p = 1) (hb : d169395 p = 1) : d170130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d169395 q = 1) : d170025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49249 q ha hb
    | true =>
      simp only [d21784, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d169395 q = 1) : d170026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d169395 q = 1) : d170031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21825 q = 1) (hb : d169395 q = 1) : d170066 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21825, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21825, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21826 q = 1) (hb : d169395 q = 1) : d170067 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21826, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21826, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21973 q = 1) (hb : d169395 q = 1) : d170130 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21973, d170130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21973, d170130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49280 (p : Pattern) (ha : d21974 p = 1) (hb : d169395 p = 1) : d170131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d169395 q = 1) : d170035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21828 q = 1) (hb : d169395 q = 1) : d170069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21828, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21828, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21829 q = 1) (hb : d169395 q = 1) : d170070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21829, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21829, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21974 q = 1) (hb : d169395 q = 1) : d170131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21974, d170131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21974, d170131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49281 (p : Pattern) (ha : d21978 p = 1) (hb : d169395 p = 1) : d170135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21863 q = 1) (hb : d169395 q = 1) : d170089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21863, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49272 q ha hb
    | true =>
      simp only [d21863, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21864 q = 1) (hb : d169395 q = 1) : d170090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21864, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21864, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21868 q = 1) (hb : d169395 q = 1) : d170094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49257 q ha hb
    | true =>
      simp only [d21868, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21869 q = 1) (hb : d169395 q = 1) : d170095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21870 q = 1) (hb : d169395 q = 1) : d170096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21870, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21870, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21871 q = 1) (hb : d169395 q = 1) : d170097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21871, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21871, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21872 q = 1) (hb : d169395 q = 1) : d170098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21872, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21872, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21978 q = 1) (hb : d169395 q = 1) : d170135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21978, d170135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21978, d170135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49282 (p : Pattern) (ha : d21979 p = 1) (hb : d169395 p = 1) : d170136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21868 q = 1) (hb : d169395 q = 1) : d170094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49257 q ha hb
    | true =>
      simp only [d21868, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21869 q = 1) (hb : d169395 q = 1) : d170095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d169395 q = 1) : d170029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49250 q ha hb
    | true =>
      simp only [d21788, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d169395 q = 1) : d170030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21874 q = 1) (hb : d169395 q = 1) : d170100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21874, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21874, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21875 q = 1) (hb : d169395 q = 1) : d170101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21875, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21875, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21876 q = 1) (hb : d169395 q = 1) : d170102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21876, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21876, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21979 q = 1) (hb : d169395 q = 1) : d170136 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21979, d170136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21979, d170136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49283 (p : Pattern) (ha : d21985 p = 1) (hb : d169395 p = 1) : d170139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21955 q = 1) (hb : d169395 q = 1) : d170112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21955, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49274 q ha hb
    | true =>
      simp only [d21955, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21956 q = 1) (hb : d169395 q = 1) : d170113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21956, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21956, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21957 q = 1) (hb : d169395 q = 1) : d170114 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21957, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21957, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21958 q = 1) (hb : d169395 q = 1) : d170115 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21958, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21958, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21959 q = 1) (hb : d169395 q = 1) : d170116 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21959, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21959, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21985 q = 1) (hb : d169395 q = 1) : d170139 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21985, d170139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21985, d170139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49284 (p : Pattern) (ha : d150164 p = 1) (hb : d169395 p = 1) : d170145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21821 q = 1) (hb : d169395 q = 1) : d170062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21821, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49266 q ha hb
    | true =>
      simp only [d21821, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49267 q ha hb
  have h2 (q : Pattern) (ha : d21822 q = 1) (hb : d169395 q = 1) : d170063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21822, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21822, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21823 q = 1) (hb : d169395 q = 1) : d170064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21823, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21823, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21824 q = 1) (hb : d169395 q = 1) : d170065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21824, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21824, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21831 q = 1) (hb : d169395 q = 1) : d170072 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21831, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49268 q ha hb
    | true =>
      simp only [d21831, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49269 q ha hb
  have h6 (q : Pattern) (ha : d21832 q = 1) (hb : d169395 q = 1) : d170073 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21832, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21832, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21833 q = 1) (hb : d169395 q = 1) : d170074 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21833, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21833, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21878 q = 1) (hb : d169395 q = 1) : d170104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21878, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49273 q ha hb
    | true =>
      simp only [d21878, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49258 q ha hb
  have h9 (q : Pattern) (ha : d150155 q = 1) (hb : d169395 q = 1) : d170105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150155, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21961 q = 1) (hb : d169395 q = 1) : d170118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21961, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49275 q ha hb
    | true =>
      simp only [d21961, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21962 q = 1) (hb : d169395 q = 1) : d170119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21962, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21962, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150156 q = 1) (hb : d169395 q = 1) : d170120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150156, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150157 q = 1) (hb : d169395 q = 1) : d170121 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150157, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150158 q = 1) (hb : d169395 q = 1) : d170122 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150158, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21969 q = 1) (hb : d169395 q = 1) : d170126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21969, d170126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49277 q ha hb
    | true =>
      simp only [d21969, d170126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49278 q ha hb
  have h16 (q : Pattern) (ha : d21970 q = 1) (hb : d169395 q = 1) : d170127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21970, d170127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21970, d170127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21971 q = 1) (hb : d169395 q = 1) : d170128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21971, d170128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21971, d170128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21972 q = 1) (hb : d169395 q = 1) : d170129 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21972, d170129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21972, d170129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21975 q = 1) (hb : d169395 q = 1) : d170132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21975, d170132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49279 q ha hb
    | true =>
      simp only [d21975, d170132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49280 q ha hb
  have h20 (q : Pattern) (ha : d21976 q = 1) (hb : d169395 q = 1) : d170133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21976, d170133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21976, d170133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21977 q = 1) (hb : d169395 q = 1) : d170134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21977, d170134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21977, d170134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21980 q = 1) (hb : d169395 q = 1) : d170137 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21980, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49281 q ha hb
    | true =>
      simp only [d21980, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49282 q ha hb
  have h23 (q : Pattern) (ha : d150160 q = 1) (hb : d169395 q = 1) : d170138 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150160, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21986 q = 1) (hb : d169395 q = 1) : d170140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21986, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49283 q ha hb
    | true =>
      simp only [d21986, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21987 q = 1) (hb : d169395 q = 1) : d170141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21987, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21987, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150161 q = 1) (hb : d169395 q = 1) : d170142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150161, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150162 q = 1) (hb : d169395 q = 1) : d170143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150162, d170143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150162, d170143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150163 q = 1) (hb : d169395 q = 1) : d170144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150163, d170144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150163, d170144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150164 q = 1) (hb : d169395 q = 1) : d170145 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150164, d170145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150164, d170145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro49285 (p : Pattern) (ha : d150171 p = 1) (hb : d169395 p = 1) : d170170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21980 q = 1) (hb : d169395 q = 1) : d170137 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21980, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49281 q ha hb
    | true =>
      simp only [d21980, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49282 q ha hb
  have h2 (q : Pattern) (ha : d150160 q = 1) (hb : d169395 q = 1) : d170138 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150160, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21986 q = 1) (hb : d169395 q = 1) : d170140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21986, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49283 q ha hb
    | true =>
      simp only [d21986, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21987 q = 1) (hb : d169395 q = 1) : d170141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21987, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21987, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150161 q = 1) (hb : d169395 q = 1) : d170142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150161, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150169 q = 1) (hb : d169395 q = 1) : d170168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150169, d170168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150169, d170168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150170 q = 1) (hb : d169395 q = 1) : d170169 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150170, d170169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150170, d170169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150171 q = 1) (hb : d169395 q = 1) : d170170 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150171, d170170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150171, d170170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49286 (p : Pattern) (ha : d22042 p = 1) (hb : d169395 p = 1) : d170180 p = 1 := by
  have h0 (q : Pattern) (ha : d22027 q = 1) (hb : d116750 q = 1) : d22027 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22032 q = 1) (hb : d169395 q = 1) : d170178 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22032, d169395, d170178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22032, d169395, d170178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22036 q = 1) (hb : d116750 q = 1) : d22036 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22040 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22041 q = 1) (hb : d169395 q = 1) : d170179 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22041, d169395, d170179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22041, d169395, d170179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22042 q = 1) (hb : d169395 q = 1) : d170180 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22042, d170180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22042, d170180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49287 (p : Pattern) (ha : d22049 p = 1) (hb : d169395 p = 1) : d170183 p = 1 := by
  have h0 (q : Pattern) (ha : d22031 q = 1) (hb : d116750 q = 1) : d22031 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22046 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22047 q = 1) (hb : d169395 q = 1) : d170181 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22047, d169395, d170181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22047, d169395, d170181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22040 q = 1) (hb : d116750 q = 1) : d22040 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13167 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22048 q = 1) (hb : d169395 q = 1) : d170182 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22048, d169395, d170182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22048, d169395, d170182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22049 q = 1) (hb : d169395 q = 1) : d170183 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22049, d170183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22049, d170183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49288 (p : Pattern) (ha : d22059 p = 1) (hb : d169395 p = 1) : d170188 p = 1 := by
  have h0 (q : Pattern) (ha : d22056 q = 1) (hb : d116750 q = 1) : d22056 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13167 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22057 q = 1) (hb : d169395 q = 1) : d170187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22057, d169395, d170187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22057, d169395, d170187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22058 q = 1) (hb : d169395 q = 1) : d22058 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22059 q = 1) (hb : d169395 q = 1) : d170188 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22059, d170188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22059, d170188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49289 (p : Pattern) (ha : d22084 p = 1) (hb : d169395 p = 1) : d170203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22050 q = 1) (hb : d169395 q = 1) : d170184 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22050, d170184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49286 q ha hb
    | true =>
      simp only [d22050, d170184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49287 q ha hb
  have h2 (q : Pattern) (ha : d22051 q = 1) (hb : d169395 q = 1) : d170185 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22051, d170185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22051, d170185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22052 q = 1) (hb : d169395 q = 1) : d170186 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22052, d170186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22052, d170186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22060 q = 1) (hb : d169395 q = 1) : d170189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22060, d170189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49287 q ha hb
    | true =>
      simp only [d22060, d170189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49288 q ha hb
  have h5 (q : Pattern) (ha : d22061 q = 1) (hb : d169395 q = 1) : d170190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22061, d170190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22061, d170190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22062 q = 1) (hb : d169395 q = 1) : d170191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22062, d170191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22062, d170191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22063 q = 1) (hb : d169395 q = 1) : d170192 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22063, d170192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22063, d170192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22070 q = 1) (hb : d169395 q = 1) : d170195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49287 q ha hb
    | true =>
      simp only [d22070, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
  have h9 (q : Pattern) (ha : d22071 q = 1) (hb : d169395 q = 1) : d170196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22072 q = 1) (hb : d169395 q = 1) : d170197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22078 q = 1) (hb : d169395 q = 1) : d22078 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d22079 q = 1) (hb : d169395 q = 1) : d170198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
    | true =>
      simp only [d22079, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22080 q = 1) (hb : d169395 q = 1) : d170199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22081 q = 1) (hb : d169395 q = 1) : d170200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22082 q = 1) (hb : d169395 q = 1) : d170201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22082, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22083 q = 1) (hb : d169395 q = 1) : d170202 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22083, d170202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22083, d170202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22084 q = 1) (hb : d169395 q = 1) : d170203 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22084, d170203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22084, d170203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro49290 (p : Pattern) (ha : d22089 p = 1) (hb : d169395 p = 1) : d170208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d169395 q = 1) : d170195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49287 q ha hb
    | true =>
      simp only [d22070, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d169395 q = 1) : d170196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d169395 q = 1) : d170197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22078 q = 1) (hb : d169395 q = 1) : d22078 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22079 q = 1) (hb : d169395 q = 1) : d170198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
    | true =>
      simp only [d22079, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22080 q = 1) (hb : d169395 q = 1) : d170199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22081 q = 1) (hb : d169395 q = 1) : d170200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22082 q = 1) (hb : d169395 q = 1) : d170201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22087 q = 1) (hb : d169395 q = 1) : d170206 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22087, d170206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22087, d170206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22088 q = 1) (hb : d169395 q = 1) : d170207 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22088, d170207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22088, d170207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22089 q = 1) (hb : d169395 q = 1) : d170208 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22089, d170208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22089, d170208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro49291 (p : Pattern) (ha : d22095 p = 1) (hb : d169395 p = 1) : d170214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22085 q = 1) (hb : d169395 q = 1) : d170204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22085, d170204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49289 q ha hb
    | true =>
      simp only [d22085, d170204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22086 q = 1) (hb : d169395 q = 1) : d170205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22086, d170205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22086, d170205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22090 q = 1) (hb : d169395 q = 1) : d170209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22090, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49290 q ha hb
    | true =>
      simp only [d22090, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22091 q = 1) (hb : d169395 q = 1) : d170210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22091, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22091, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22092 q = 1) (hb : d169395 q = 1) : d170211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22092, d170211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22092, d170211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22093 q = 1) (hb : d169395 q = 1) : d170212 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22093, d170212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22093, d170212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22094 q = 1) (hb : d169395 q = 1) : d170213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22094, d170213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22094, d170213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22095 q = 1) (hb : d169395 q = 1) : d170214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22095, d170214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22095, d170214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49292 (p : Pattern) (ha : d22109 p = 1) (hb : d169395 p = 1) : d170226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22090 q = 1) (hb : d169395 q = 1) : d170209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22090, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49290 q ha hb
    | true =>
      simp only [d22090, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22091 q = 1) (hb : d169395 q = 1) : d170210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22091, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22091, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d169395 q = 1) : d170221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49263 q ha hb
    | true =>
      simp only [d22104, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d169395 q = 1) : d170222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22106 q = 1) (hb : d169395 q = 1) : d170223 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22106, d170223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22106, d170223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22107 q = 1) (hb : d169395 q = 1) : d170224 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22107, d170224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22107, d170224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22108 q = 1) (hb : d169395 q = 1) : d170225 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22108, d170225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22108, d170225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22109 q = 1) (hb : d169395 q = 1) : d170226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22109, d170226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22109, d170226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49293 (p : Pattern) (ha : d22180 p = 1) (hb : d169395 p = 1) : d170234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d169395 q = 1) : d170195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49287 q ha hb
    | true =>
      simp only [d22070, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d169395 q = 1) : d170196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d169395 q = 1) : d170197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22078 q = 1) (hb : d169395 q = 1) : d22078 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22079 q = 1) (hb : d169395 q = 1) : d170198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
    | true =>
      simp only [d22079, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22080 q = 1) (hb : d169395 q = 1) : d170199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22081 q = 1) (hb : d169395 q = 1) : d170200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22082 q = 1) (hb : d169395 q = 1) : d170201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22174 q = 1) (hb : d169395 q = 1) : d22174 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22175 q = 1) (hb : d169395 q = 1) : d170229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22175, d170229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
    | true =>
      simp only [d22175, d170229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22176 q = 1) (hb : d169395 q = 1) : d170230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22176, d170230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22176, d170230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22177 q = 1) (hb : d169395 q = 1) : d170231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22177, d170231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22177, d170231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22178 q = 1) (hb : d169395 q = 1) : d170232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22178, d170232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22178, d170232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22179 q = 1) (hb : d169395 q = 1) : d170233 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22179, d170233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22179, d170233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22180 q = 1) (hb : d169395 q = 1) : d170234 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22180, d170234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22180, d170234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro49294 (p : Pattern) (ha : d22186 p = 1) (hb : d169395 p = 1) : d170240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22181 q = 1) (hb : d169395 q = 1) : d170235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22181, d170235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49293 q ha hb
    | true =>
      simp only [d22181, d170235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22182 q = 1) (hb : d169395 q = 1) : d170236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22182, d170236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22182, d170236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22183 q = 1) (hb : d169395 q = 1) : d170237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22183, d170237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22183, d170237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22184 q = 1) (hb : d169395 q = 1) : d170238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22184, d170238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22184, d170238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22185 q = 1) (hb : d169395 q = 1) : d170239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22185, d170239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22185, d170239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22186 q = 1) (hb : d169395 q = 1) : d170240 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22186, d170240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22186, d170240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49295 (p : Pattern) (ha : d150181 p = 1) (hb : d169395 p = 1) : d170246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22110 q = 1) (hb : d169395 q = 1) : d170227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22110, d170227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49291 q ha hb
    | true =>
      simp only [d22110, d170227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49292 q ha hb
  have h2 (q : Pattern) (ha : d150177 q = 1) (hb : d169395 q = 1) : d170228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150177, d170228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150177, d170228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22187 q = 1) (hb : d169395 q = 1) : d170241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22187, d170241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49294 q ha hb
    | true =>
      simp only [d22187, d170241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22188 q = 1) (hb : d169395 q = 1) : d170242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22188, d170242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22188, d170242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150178 q = 1) (hb : d169395 q = 1) : d170243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150178, d170243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150178, d170243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150179 q = 1) (hb : d169395 q = 1) : d170244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150179, d170244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150179, d170244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150180 q = 1) (hb : d169395 q = 1) : d170245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150180, d170245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150180, d170245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150181 q = 1) (hb : d169395 q = 1) : d170246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150181, d170246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150181, d170246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49296 (p : Pattern) (ha : d150187 p = 1) (hb : d169395 p = 1) : d170263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21804 q = 1) (hb : d169395 q = 1) : d170045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21804, d170045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21804, d170045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49253 q ha hb
  have h2 (q : Pattern) (ha : d21805 q = 1) (hb : d169395 q = 1) : d170046 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21805, d170046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21805, d170046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21814 q = 1) (hb : d169395 q = 1) : d170055 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49253 q ha hb
    | true =>
      simp only [d21814, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49256 q ha hb
  have h4 (q : Pattern) (ha : d21815 q = 1) (hb : d169395 q = 1) : d170056 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21815, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21816 q = 1) (hb : d169395 q = 1) : d170057 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21816, d170057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21816, d170057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150165 q = 1) (hb : d169395 q = 1) : d170146 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150165, d170146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49276 q ha hb
    | true =>
      simp only [d150165, d170146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49284 q ha hb
  have h7 (q : Pattern) (ha : d22010 q = 1) (hb : d169395 q = 1) : d170164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22010, d170164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49259 q ha hb
    | true =>
      simp only [d22010, d170164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49260 q ha hb
  have h8 (q : Pattern) (ha : d150166 q = 1) (hb : d169395 q = 1) : d170165 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150166, d170165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150166, d170165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150167 q = 1) (hb : d169395 q = 1) : d170166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150167, d170166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150167, d170166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150168 q = 1) (hb : d169395 q = 1) : d170167 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150168, d170167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150168, d170167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150172 q = 1) (hb : d169395 q = 1) : d170171 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150172, d170171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150172, d170171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49285 q ha hb
  have h12 (q : Pattern) (ha : d22019 q = 1) (hb : d169395 q = 1) : d170173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22019, d170173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22019, d170173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49261 q ha hb
  have h13 (q : Pattern) (ha : d150173 q = 1) (hb : d169395 q = 1) : d170174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150173, d170174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150173, d170174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150174 q = 1) (hb : d169395 q = 1) : d170175 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150174, d170175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150174, d170175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150175 q = 1) (hb : d169395 q = 1) : d170176 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150175, d170176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150175, d170176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150176 q = 1) (hb : d169395 q = 1) : d170177 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150176, d170177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150176, d170177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150182 q = 1) (hb : d169395 q = 1) : d170247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150182, d170247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150182, d170247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49295 q ha hb
  have h18 (q : Pattern) (ha : d22204 q = 1) (hb : d169395 q = 1) : d170258 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22204, d170258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22204, d170258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49265 q ha hb
  have h19 (q : Pattern) (ha : d150183 q = 1) (hb : d169395 q = 1) : d170259 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150183, d170259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150183, d170259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150184 q = 1) (hb : d169395 q = 1) : d170260 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150184, d170260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150184, d170260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150185 q = 1) (hb : d169395 q = 1) : d170261 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150185, d170261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150185, d170261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150186 q = 1) (hb : d169395 q = 1) : d170262 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150186, d170262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150186, d170262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150187 q = 1) (hb : d169395 q = 1) : d170263 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150187, d170263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150187, d170263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49297 (p : Pattern) (ha : d150193 p = 1) (hb : d169395 p = 1) : d170269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150188 q = 1) (hb : d169395 q = 1) : d170264 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150188, d170264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150188, d170264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49296 q ha hb
  have h2 (q : Pattern) (ha : d150189 q = 1) (hb : d169395 q = 1) : d170265 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150189, d170265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150189, d170265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150190 q = 1) (hb : d169395 q = 1) : d170266 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150190, d170266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150190, d170266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150191 q = 1) (hb : d169395 q = 1) : d170267 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150191, d170267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150191, d170267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150192 q = 1) (hb : d169395 q = 1) : d170268 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150192, d170268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150192, d170268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150193 q = 1) (hb : d169395 q = 1) : d170269 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150193, d170269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150193, d170269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49298 (p : Pattern) (ha : d22231 p = 1) (hb : d169395 p = 1) : d170275 p = 1 := by
  have h0 (q : Pattern) (ha : d16860 q = 1) (hb : d116750 q = 1) : d16860 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22223 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22224 q = 1) (hb : d169395 q = 1) : d170273 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22224, d169395, d170273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22224, d169395, d170273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22229 q = 1) (hb : d116750 q = 1) : d22229 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13354 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22230 q = 1) (hb : d169395 q = 1) : d170274 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22230, d169395, d170274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22230, d169395, d170274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22231 q = 1) (hb : d169395 q = 1) : d170275 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22231, d170275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22231, d170275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49299 (p : Pattern) (ha : d22239 p = 1) (hb : d169395 p = 1) : d170277 p = 1 := by
  have h0 (q : Pattern) (ha : d22223 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22236 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22237 q = 1) (hb : d169395 q = 1) : d170276 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22237, d169395, d170276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22237, d169395, d170276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22238 q = 1) (hb : d169395 q = 1) : d22238 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22239 q = 1) (hb : d169395 q = 1) : d170277 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22239, d170277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22239, d170277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49300 (p : Pattern) (ha : d22261 p = 1) (hb : d169395 p = 1) : d170290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d169395 q = 1) : d170278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49298 q ha hb
    | true =>
      simp only [d22240, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d169395 q = 1) : d170279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d169395 q = 1) : d170280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22249 q = 1) (hb : d169395 q = 1) : d22249 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22250 q = 1) (hb : d169395 q = 1) : d170281 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
    | true =>
      simp only [d22250, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22251 q = 1) (hb : d169395 q = 1) : d170282 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22252 q = 1) (hb : d169395 q = 1) : d170283 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22253 q = 1) (hb : d169395 q = 1) : d170284 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22255 q = 1) (hb : d169395 q = 1) : d22255 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22256 q = 1) (hb : d169395 q = 1) : d170285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22256, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
    | true =>
      simp only [d22256, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22257 q = 1) (hb : d169395 q = 1) : d170286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22257, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22257, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22258 q = 1) (hb : d169395 q = 1) : d170287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22258, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22258, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22259 q = 1) (hb : d169395 q = 1) : d170288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22259, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22259, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22260 q = 1) (hb : d169395 q = 1) : d170289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22260, d170289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22260, d170289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22261 q = 1) (hb : d169395 q = 1) : d170290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22261, d170290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22261, d170290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro49301 (p : Pattern) (ha : d22265 p = 1) (hb : d169395 p = 1) : d170294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22255 q = 1) (hb : d169395 q = 1) : d22255 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22256 q = 1) (hb : d169395 q = 1) : d170285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22256, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
    | true =>
      simp only [d22256, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22257 q = 1) (hb : d169395 q = 1) : d170286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22257, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22257, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22258 q = 1) (hb : d169395 q = 1) : d170287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22258, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22258, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22259 q = 1) (hb : d169395 q = 1) : d170288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22259, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22259, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22264 q = 1) (hb : d169395 q = 1) : d170293 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22264, d170293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22264, d170293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22265 q = 1) (hb : d169395 q = 1) : d170294 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22265, d170294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22265, d170294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49302 (p : Pattern) (ha : d22271 p = 1) (hb : d169395 p = 1) : d170300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49300 q ha hb
    | true =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d169395 q = 1) : d170298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22270 q = 1) (hb : d169395 q = 1) : d170299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22270, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22270, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22271 q = 1) (hb : d169395 q = 1) : d170300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22271, d170300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22271, d170300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49303 (p : Pattern) (ha : d22275 p = 1) (hb : d169395 p = 1) : d170304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d169395 q = 1) : d170302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22274 q = 1) (hb : d169395 q = 1) : d170303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22274, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22274, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22275 q = 1) (hb : d169395 q = 1) : d170304 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22275, d170304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22275, d170304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49304 (p : Pattern) (ha : d22281 p = 1) (hb : d169395 p = 1) : d170310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22276 q = 1) (hb : d169395 q = 1) : d170305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49302 q ha hb
    | true =>
      simp only [d22276, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49303 q ha hb
  have h2 (q : Pattern) (ha : d22277 q = 1) (hb : d169395 q = 1) : d170306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22277, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22278 q = 1) (hb : d169395 q = 1) : d170307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22278, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22279 q = 1) (hb : d169395 q = 1) : d170308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22279, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22280 q = 1) (hb : d169395 q = 1) : d170309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22281 q = 1) (hb : d169395 q = 1) : d170310 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22281, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22281, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49305 (p : Pattern) (ha : d22284 p = 1) (hb : d169395 p = 1) : d170313 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49300 q ha hb
    | true =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d169395 q = 1) : d170298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22270 q = 1) (hb : d169395 q = 1) : d170299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22270, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22270, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22284 q = 1) (hb : d169395 q = 1) : d170313 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22284, d170313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22284, d170313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49306 (p : Pattern) (ha : d22285 p = 1) (hb : d169395 p = 1) : d170314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d169395 q = 1) : d170302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22274 q = 1) (hb : d169395 q = 1) : d170303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22274, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22274, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22285 q = 1) (hb : d169395 q = 1) : d170314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22285, d170314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22285, d170314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49307 (p : Pattern) (ha : d22291 p = 1) (hb : d169395 p = 1) : d170320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22276 q = 1) (hb : d169395 q = 1) : d170305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49302 q ha hb
    | true =>
      simp only [d22276, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49303 q ha hb
  have h2 (q : Pattern) (ha : d22277 q = 1) (hb : d169395 q = 1) : d170306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22277, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22278 q = 1) (hb : d169395 q = 1) : d170307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22278, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22279 q = 1) (hb : d169395 q = 1) : d170308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22279, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22280 q = 1) (hb : d169395 q = 1) : d170309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22286 q = 1) (hb : d169395 q = 1) : d170315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49305 q ha hb
    | true =>
      simp only [d22286, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49306 q ha hb
  have h7 (q : Pattern) (ha : d22287 q = 1) (hb : d169395 q = 1) : d170316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22288 q = 1) (hb : d169395 q = 1) : d170317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22288, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22289 q = 1) (hb : d169395 q = 1) : d170318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22290 q = 1) (hb : d169395 q = 1) : d170319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22291 q = 1) (hb : d169395 q = 1) : d170320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22291, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22291, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49308 (p : Pattern) (ha : d22340 p = 1) (hb : d169395 p = 1) : d170358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d169395 q = 1) : d170278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49298 q ha hb
    | true =>
      simp only [d22240, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d169395 q = 1) : d170279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d169395 q = 1) : d170280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22249 q = 1) (hb : d169395 q = 1) : d22249 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22250 q = 1) (hb : d169395 q = 1) : d170281 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
    | true =>
      simp only [d22250, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22251 q = 1) (hb : d169395 q = 1) : d170282 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22252 q = 1) (hb : d169395 q = 1) : d170283 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22253 q = 1) (hb : d169395 q = 1) : d170284 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22338 q = 1) (hb : d169395 q = 1) : d170356 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22338, d170356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22338, d170356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22339 q = 1) (hb : d169395 q = 1) : d170357 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22339, d170357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22339, d170357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22340 q = 1) (hb : d169395 q = 1) : d170358 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22340, d170358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22340, d170358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro49309 (p : Pattern) (ha : d22350 p = 1) (hb : d169395 p = 1) : d170368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22341 q = 1) (hb : d169395 q = 1) : d170359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49308 q ha hb
    | true =>
      simp only [d22341, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22342 q = 1) (hb : d169395 q = 1) : d170360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22347 q = 1) (hb : d169395 q = 1) : d170365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22347, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22347, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22348 q = 1) (hb : d169395 q = 1) : d170366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22348, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22348, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22349 q = 1) (hb : d169395 q = 1) : d170367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22349, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22349, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22350 q = 1) (hb : d169395 q = 1) : d170368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22350, d170368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22350, d170368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49310 (p : Pattern) (ha : d22476 p = 1) (hb : d169395 p = 1) : d170422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22466 q = 1) (hb : d169395 q = 1) : d170412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22466, d170412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49309 q ha hb
    | true =>
      simp only [d22466, d170412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49303 q ha hb
  have h2 (q : Pattern) (ha : d22467 q = 1) (hb : d169395 q = 1) : d170413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22467, d170413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22467, d170413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22468 q = 1) (hb : d169395 q = 1) : d170414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22468, d170414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22468, d170414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22469 q = 1) (hb : d169395 q = 1) : d170415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22469, d170415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22469, d170415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22470 q = 1) (hb : d169395 q = 1) : d170416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22470, d170416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22470, d170416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22471 q = 1) (hb : d169395 q = 1) : d170417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22471, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49303 q ha hb
    | true =>
      simp only [d22471, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22472 q = 1) (hb : d169395 q = 1) : d170418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22472, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22472, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22473 q = 1) (hb : d169395 q = 1) : d170419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22473, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22473, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22474 q = 1) (hb : d169395 q = 1) : d170420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22474, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22474, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22475 q = 1) (hb : d169395 q = 1) : d170421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22475, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22475, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22476 q = 1) (hb : d169395 q = 1) : d170422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22476, d170422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22476, d170422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49311 (p : Pattern) (ha : d22482 p = 1) (hb : d169395 p = 1) : d170428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22471 q = 1) (hb : d169395 q = 1) : d170417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22471, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49303 q ha hb
    | true =>
      simp only [d22471, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22472 q = 1) (hb : d169395 q = 1) : d170418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22472, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22472, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22473 q = 1) (hb : d169395 q = 1) : d170419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22473, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22473, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22474 q = 1) (hb : d169395 q = 1) : d170420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22474, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22474, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22475 q = 1) (hb : d169395 q = 1) : d170421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22475, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22475, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22477 q = 1) (hb : d169395 q = 1) : d170423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22477, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49306 q ha hb
    | true =>
      simp only [d22477, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22478 q = 1) (hb : d169395 q = 1) : d170424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22478, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22478, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22479 q = 1) (hb : d169395 q = 1) : d170425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22479, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22479, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22480 q = 1) (hb : d169395 q = 1) : d170426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22480, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22480, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22481 q = 1) (hb : d169395 q = 1) : d170427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22481, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22481, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22482 q = 1) (hb : d169395 q = 1) : d170428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22482, d170428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22482, d170428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49312 (p : Pattern) (ha : d22491 p = 1) (hb : d169395 p = 1) : d170437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22477 q = 1) (hb : d169395 q = 1) : d170423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22477, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49306 q ha hb
    | true =>
      simp only [d22477, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22478 q = 1) (hb : d169395 q = 1) : d170424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22478, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22478, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22479 q = 1) (hb : d169395 q = 1) : d170425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22479, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22479, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22480 q = 1) (hb : d169395 q = 1) : d170426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22480, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22480, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22481 q = 1) (hb : d169395 q = 1) : d170427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22481, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22481, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22491 q = 1) (hb : d169395 q = 1) : d170437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22491, d170437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22491, d170437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49313 (p : Pattern) (ha : d22534 p = 1) (hb : d169395 p = 1) : d170458 p = 1 := by
  have h0 (q : Pattern) (ha : d22511 q = 1) (hb : d116750 q = 1) : d22511 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22533 q = 1) (hb : d169395 q = 1) : d170457 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22533, d169395, d170457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22533, d169395, d170457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22523 q = 1) (hb : d169395 q = 1) : d22523 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22534 q = 1) (hb : d169395 q = 1) : d170458 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22534, d170458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22534, d170458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49314 (p : Pattern) (ha : d22568 p = 1) (hb : d169395 p = 1) : d170484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22562 q = 1) (hb : d169395 q = 1) : d22562 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22563 q = 1) (hb : d169395 q = 1) : d170479 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
    | true =>
      simp only [d22563, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22564 q = 1) (hb : d169395 q = 1) : d170480 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22565 q = 1) (hb : d169395 q = 1) : d170481 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22566 q = 1) (hb : d169395 q = 1) : d170482 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22566, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22567 q = 1) (hb : d169395 q = 1) : d170483 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22567, d170483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22567, d170483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22568 q = 1) (hb : d169395 q = 1) : d170484 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22568, d170484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22568, d170484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49315 (p : Pattern) (ha : d22662 p = 1) (hb : d169395 p = 1) : d170515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22569 q = 1) (hb : d169395 q = 1) : d170485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49314 q ha hb
    | true =>
      simp only [d22569, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22570 q = 1) (hb : d169395 q = 1) : d170486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22659 q = 1) (hb : d169395 q = 1) : d170512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22659, d170512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22659, d170512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22660 q = 1) (hb : d169395 q = 1) : d170513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22660, d170513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22660, d170513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22661 q = 1) (hb : d169395 q = 1) : d170514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22661, d170514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22661, d170514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22662 q = 1) (hb : d169395 q = 1) : d170515 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22662, d170515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22662, d170515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49316 (p : Pattern) (ha : d22668 p = 1) (hb : d169395 p = 1) : d170521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22663 q = 1) (hb : d169395 q = 1) : d170516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22663, d170516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49315 q ha hb
    | true =>
      simp only [d22663, d170516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22664 q = 1) (hb : d169395 q = 1) : d170517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22664, d170517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22664, d170517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22665 q = 1) (hb : d169395 q = 1) : d170518 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22665, d170518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22665, d170518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22666 q = 1) (hb : d169395 q = 1) : d170519 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22666, d170519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22666, d170519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22667 q = 1) (hb : d169395 q = 1) : d170520 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22667, d170520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22667, d170520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22668 q = 1) (hb : d169395 q = 1) : d170521 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22668, d170521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22668, d170521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49317 (p : Pattern) (ha : d22296 p = 1) (hb : d169395 p = 1) : d170325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49300 q ha hb
    | true =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d169395 q = 1) : d170298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22295 q = 1) (hb : d169395 q = 1) : d170324 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22295, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22295, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22296 q = 1) (hb : d169395 q = 1) : d170325 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22296, d170325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22296, d170325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49318 (p : Pattern) (ha : d22298 p = 1) (hb : d169395 p = 1) : d170327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d169395 q = 1) : d170302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22297 q = 1) (hb : d169395 q = 1) : d170326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22297, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22297, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22298 q = 1) (hb : d169395 q = 1) : d170327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22298, d170327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22298, d170327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49319 (p : Pattern) (ha : d22305 p = 1) (hb : d169395 p = 1) : d170334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49300 q ha hb
    | true =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22303 q = 1) (hb : d169395 q = 1) : d170332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22303, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22303, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22304 q = 1) (hb : d169395 q = 1) : d170333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22304, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22304, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22305 q = 1) (hb : d169395 q = 1) : d170334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22305, d170334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22305, d170334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49320 (p : Pattern) (ha : d22308 p = 1) (hb : d169395 p = 1) : d170337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22306 q = 1) (hb : d169395 q = 1) : d170335 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22306, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22306, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22307 q = 1) (hb : d169395 q = 1) : d170336 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22307, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22307, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22308 q = 1) (hb : d169395 q = 1) : d170337 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22308, d170337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22308, d170337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49321 (p : Pattern) (ha : d22319 p = 1) (hb : d169395 p = 1) : d170342 p = 1 := by
  have h0 (q : Pattern) (ha : d22316 q = 1) (hb : d116750 q = 1) : d22316 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22317 q = 1) (hb : d169395 q = 1) : d170341 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22317, d169395, d170341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22317, d169395, d170341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15230 q = 1) (hb : d116750 q = 1) : d15230 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22229 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22318 q = 1) (hb : d169395 q = 1) : d15231 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22318, d169395, d15231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22318, d169395, d15231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22319 q = 1) (hb : d169395 q = 1) : d170342 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22319, d170342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22319, d170342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49322 (p : Pattern) (ha : d22329 p = 1) (hb : d169395 p = 1) : d170347 p = 1 := by
  have h0 (q : Pattern) (ha : d22327 q = 1) (hb : d116750 q = 1) : d22327 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13354 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22328 q = 1) (hb : d169395 q = 1) : d170346 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22328, d169395, d170346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22328, d169395, d170346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22238 q = 1) (hb : d169395 q = 1) : d22238 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22329 q = 1) (hb : d169395 q = 1) : d170347 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22329, d170347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22329, d170347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49323 (p : Pattern) (ha : d22335 p = 1) (hb : d169395 p = 1) : d170353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22320 q = 1) (hb : d169395 q = 1) : d170343 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22320, d170343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49321 q ha hb
    | true =>
      simp only [d22320, d170343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49298 q ha hb
  have h2 (q : Pattern) (ha : d22321 q = 1) (hb : d169395 q = 1) : d170344 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22321, d170344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22321, d170344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22322 q = 1) (hb : d169395 q = 1) : d170345 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22322, d170345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22322, d170345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22330 q = 1) (hb : d169395 q = 1) : d170348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22330, d170348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49298 q ha hb
    | true =>
      simp only [d22330, d170348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49322 q ha hb
  have h5 (q : Pattern) (ha : d22331 q = 1) (hb : d169395 q = 1) : d170349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22331, d170349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22331, d170349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22332 q = 1) (hb : d169395 q = 1) : d170350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22332, d170350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22332, d170350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22333 q = 1) (hb : d169395 q = 1) : d170351 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22333, d170351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22333, d170351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22240 q = 1) (hb : d169395 q = 1) : d170278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49298 q ha hb
    | true =>
      simp only [d22240, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
  have h9 (q : Pattern) (ha : d22241 q = 1) (hb : d169395 q = 1) : d170279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22242 q = 1) (hb : d169395 q = 1) : d170280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22249 q = 1) (hb : d169395 q = 1) : d22249 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d22250 q = 1) (hb : d169395 q = 1) : d170281 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
    | true =>
      simp only [d22250, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22251 q = 1) (hb : d169395 q = 1) : d170282 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22252 q = 1) (hb : d169395 q = 1) : d170283 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22253 q = 1) (hb : d169395 q = 1) : d170284 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22253, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22334 q = 1) (hb : d169395 q = 1) : d170352 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22334, d170352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22334, d170352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22335 q = 1) (hb : d169395 q = 1) : d170353 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22335, d170353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22335, d170353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro49324 (p : Pattern) (ha : d22346 p = 1) (hb : d169395 p = 1) : d170364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22336 q = 1) (hb : d169395 q = 1) : d170354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22336, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49323 q ha hb
    | true =>
      simp only [d22336, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22337 q = 1) (hb : d169395 q = 1) : d170355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22337, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22337, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22341 q = 1) (hb : d169395 q = 1) : d170359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49308 q ha hb
    | true =>
      simp only [d22341, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22342 q = 1) (hb : d169395 q = 1) : d170360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22343 q = 1) (hb : d169395 q = 1) : d170361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22343, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22343, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22344 q = 1) (hb : d169395 q = 1) : d170362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22344, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22344, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22345 q = 1) (hb : d169395 q = 1) : d170363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22345, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22345, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22346 q = 1) (hb : d169395 q = 1) : d170364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22346, d170364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22346, d170364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49325 (p : Pattern) (ha : d22427 p = 1) (hb : d169395 p = 1) : d170376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d169395 q = 1) : d170278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49298 q ha hb
    | true =>
      simp only [d22240, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d169395 q = 1) : d170279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d169395 q = 1) : d170280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22249 q = 1) (hb : d169395 q = 1) : d22249 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22250 q = 1) (hb : d169395 q = 1) : d170281 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
    | true =>
      simp only [d22250, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22251 q = 1) (hb : d169395 q = 1) : d170282 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22252 q = 1) (hb : d169395 q = 1) : d170283 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22253 q = 1) (hb : d169395 q = 1) : d170284 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22421 q = 1) (hb : d169395 q = 1) : d22421 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22422 q = 1) (hb : d169395 q = 1) : d170371 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22422, d170371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49299 q ha hb
    | true =>
      simp only [d22422, d170371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22423 q = 1) (hb : d169395 q = 1) : d170372 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22423, d170372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22423, d170372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22424 q = 1) (hb : d169395 q = 1) : d170373 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22424, d170373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22424, d170373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22425 q = 1) (hb : d169395 q = 1) : d170374 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22425, d170374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22425, d170374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22426 q = 1) (hb : d169395 q = 1) : d170375 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22426, d170375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22426, d170375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22427 q = 1) (hb : d169395 q = 1) : d170376 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22427, d170376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22427, d170376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro49326 (p : Pattern) (ha : d22433 p = 1) (hb : d169395 p = 1) : d170382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22428 q = 1) (hb : d169395 q = 1) : d170377 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22428, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49325 q ha hb
    | true =>
      simp only [d22428, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22429 q = 1) (hb : d169395 q = 1) : d170378 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22429, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22429, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22430 q = 1) (hb : d169395 q = 1) : d170379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22430, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22430, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22431 q = 1) (hb : d169395 q = 1) : d170380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22431, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22431, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22432 q = 1) (hb : d169395 q = 1) : d170381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22432, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22432, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22433 q = 1) (hb : d169395 q = 1) : d170382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22433, d170382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22433, d170382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49327 (p : Pattern) (ha : d150201 p = 1) (hb : d169395 p = 1) : d170388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22299 q = 1) (hb : d169395 q = 1) : d170328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22299, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49317 q ha hb
    | true =>
      simp only [d22299, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49318 q ha hb
  have h2 (q : Pattern) (ha : d22300 q = 1) (hb : d169395 q = 1) : d170329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22300, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22300, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22301 q = 1) (hb : d169395 q = 1) : d170330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22301, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22301, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22302 q = 1) (hb : d169395 q = 1) : d170331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22302, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22302, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22309 q = 1) (hb : d169395 q = 1) : d170338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22309, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49319 q ha hb
    | true =>
      simp only [d22309, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49320 q ha hb
  have h6 (q : Pattern) (ha : d22310 q = 1) (hb : d169395 q = 1) : d170339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22310, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22310, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22311 q = 1) (hb : d169395 q = 1) : d170340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22311, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22311, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22351 q = 1) (hb : d169395 q = 1) : d170369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22351, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49324 q ha hb
    | true =>
      simp only [d22351, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49309 q ha hb
  have h9 (q : Pattern) (ha : d150197 q = 1) (hb : d169395 q = 1) : d170370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150197, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22434 q = 1) (hb : d169395 q = 1) : d170383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22434, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49326 q ha hb
    | true =>
      simp only [d22434, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22435 q = 1) (hb : d169395 q = 1) : d170384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22435, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22435, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150198 q = 1) (hb : d169395 q = 1) : d170385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150198, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150199 q = 1) (hb : d169395 q = 1) : d170386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150199, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150200 q = 1) (hb : d169395 q = 1) : d170387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150200, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150201 q = 1) (hb : d169395 q = 1) : d170388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150201, d170388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150201, d170388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49328 (p : Pattern) (ha : d22440 p = 1) (hb : d169395 p = 1) : d170389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49300 q ha hb
    | true =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d169395 q = 1) : d170298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22295 q = 1) (hb : d169395 q = 1) : d170324 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22295, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22295, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22440 q = 1) (hb : d169395 q = 1) : d170389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22440, d170389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22440, d170389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49329 (p : Pattern) (ha : d22441 p = 1) (hb : d169395 p = 1) : d170390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d169395 q = 1) : d170302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22297 q = 1) (hb : d169395 q = 1) : d170326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22297, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22297, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22441 q = 1) (hb : d169395 q = 1) : d170390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22441, d170390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22441, d170390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49330 (p : Pattern) (ha : d22446 p = 1) (hb : d169395 p = 1) : d170395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49300 q ha hb
    | true =>
      simp only [d22262, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22303 q = 1) (hb : d169395 q = 1) : d170332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22303, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22303, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22304 q = 1) (hb : d169395 q = 1) : d170333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22304, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22304, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22446 q = 1) (hb : d169395 q = 1) : d170395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22446, d170395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22446, d170395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49331 (p : Pattern) (ha : d22447 p = 1) (hb : d169395 p = 1) : d170396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22306 q = 1) (hb : d169395 q = 1) : d170335 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22306, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22306, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22307 q = 1) (hb : d169395 q = 1) : d170336 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22307, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22307, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22447 q = 1) (hb : d169395 q = 1) : d170396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22447, d170396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22447, d170396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49332 (p : Pattern) (ha : d22451 p = 1) (hb : d169395 p = 1) : d170400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22336 q = 1) (hb : d169395 q = 1) : d170354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22336, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49323 q ha hb
    | true =>
      simp only [d22336, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22337 q = 1) (hb : d169395 q = 1) : d170355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22337, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22337, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22341 q = 1) (hb : d169395 q = 1) : d170359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49308 q ha hb
    | true =>
      simp only [d22341, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22342 q = 1) (hb : d169395 q = 1) : d170360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22343 q = 1) (hb : d169395 q = 1) : d170361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22343, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22343, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22344 q = 1) (hb : d169395 q = 1) : d170362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22344, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22344, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22345 q = 1) (hb : d169395 q = 1) : d170363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22345, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22345, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22451 q = 1) (hb : d169395 q = 1) : d170400 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22451, d170400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22451, d170400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49333 (p : Pattern) (ha : d22452 p = 1) (hb : d169395 p = 1) : d170401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22341 q = 1) (hb : d169395 q = 1) : d170359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49308 q ha hb
    | true =>
      simp only [d22341, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22342 q = 1) (hb : d169395 q = 1) : d170360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49301 q ha hb
    | true =>
      simp only [d22266, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22347 q = 1) (hb : d169395 q = 1) : d170365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22347, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22347, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22348 q = 1) (hb : d169395 q = 1) : d170366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22348, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22348, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22349 q = 1) (hb : d169395 q = 1) : d170367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22349, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22349, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22452 q = 1) (hb : d169395 q = 1) : d170401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22452, d170401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22452, d170401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49334 (p : Pattern) (ha : d22458 p = 1) (hb : d169395 p = 1) : d170404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22428 q = 1) (hb : d169395 q = 1) : d170377 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22428, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49325 q ha hb
    | true =>
      simp only [d22428, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22429 q = 1) (hb : d169395 q = 1) : d170378 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22429, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22429, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22430 q = 1) (hb : d169395 q = 1) : d170379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22430, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22430, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22431 q = 1) (hb : d169395 q = 1) : d170380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22431, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22431, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22432 q = 1) (hb : d169395 q = 1) : d170381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22432, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22432, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22458 q = 1) (hb : d169395 q = 1) : d170404 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22458, d170404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22458, d170404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49335 (p : Pattern) (ha : d150206 p = 1) (hb : d169395 p = 1) : d170410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22299 q = 1) (hb : d169395 q = 1) : d170328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22299, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49317 q ha hb
    | true =>
      simp only [d22299, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49318 q ha hb
  have h2 (q : Pattern) (ha : d22300 q = 1) (hb : d169395 q = 1) : d170329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22300, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22300, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22301 q = 1) (hb : d169395 q = 1) : d170330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22301, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22301, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22302 q = 1) (hb : d169395 q = 1) : d170331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22302, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22302, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22309 q = 1) (hb : d169395 q = 1) : d170338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22309, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49319 q ha hb
    | true =>
      simp only [d22309, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49320 q ha hb
  have h6 (q : Pattern) (ha : d22310 q = 1) (hb : d169395 q = 1) : d170339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22310, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22310, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22311 q = 1) (hb : d169395 q = 1) : d170340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22311, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22311, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22351 q = 1) (hb : d169395 q = 1) : d170369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22351, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49324 q ha hb
    | true =>
      simp only [d22351, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49309 q ha hb
  have h9 (q : Pattern) (ha : d150197 q = 1) (hb : d169395 q = 1) : d170370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150197, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22434 q = 1) (hb : d169395 q = 1) : d170383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22434, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49326 q ha hb
    | true =>
      simp only [d22434, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22435 q = 1) (hb : d169395 q = 1) : d170384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22435, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22435, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150198 q = 1) (hb : d169395 q = 1) : d170385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150198, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150199 q = 1) (hb : d169395 q = 1) : d170386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150199, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150200 q = 1) (hb : d169395 q = 1) : d170387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150200, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22442 q = 1) (hb : d169395 q = 1) : d170391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22442, d170391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49328 q ha hb
    | true =>
      simp only [d22442, d170391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49329 q ha hb
  have h16 (q : Pattern) (ha : d22443 q = 1) (hb : d169395 q = 1) : d170392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22443, d170392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22443, d170392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22444 q = 1) (hb : d169395 q = 1) : d170393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22444, d170393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22444, d170393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22445 q = 1) (hb : d169395 q = 1) : d170394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22445, d170394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22445, d170394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22448 q = 1) (hb : d169395 q = 1) : d170397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22448, d170397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49330 q ha hb
    | true =>
      simp only [d22448, d170397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49331 q ha hb
  have h20 (q : Pattern) (ha : d22449 q = 1) (hb : d169395 q = 1) : d170398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22449, d170398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22449, d170398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d22450 q = 1) (hb : d169395 q = 1) : d170399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22450, d170399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22450, d170399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22453 q = 1) (hb : d169395 q = 1) : d170402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22453, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49332 q ha hb
    | true =>
      simp only [d22453, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49333 q ha hb
  have h23 (q : Pattern) (ha : d150202 q = 1) (hb : d169395 q = 1) : d170403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150202, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d22459 q = 1) (hb : d169395 q = 1) : d170405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22459, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49334 q ha hb
    | true =>
      simp only [d22459, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d22460 q = 1) (hb : d169395 q = 1) : d170406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22460, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22460, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150203 q = 1) (hb : d169395 q = 1) : d170407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150203, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150204 q = 1) (hb : d169395 q = 1) : d170408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150204, d170408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150204, d170408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150205 q = 1) (hb : d169395 q = 1) : d170409 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150205, d170409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150205, d170409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150206 q = 1) (hb : d169395 q = 1) : d170410 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150206, d170410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150206, d170410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro49336 (p : Pattern) (ha : d150213 p = 1) (hb : d169395 p = 1) : d170435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22453 q = 1) (hb : d169395 q = 1) : d170402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22453, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49332 q ha hb
    | true =>
      simp only [d22453, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49333 q ha hb
  have h2 (q : Pattern) (ha : d150202 q = 1) (hb : d169395 q = 1) : d170403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150202, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22459 q = 1) (hb : d169395 q = 1) : d170405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22459, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49334 q ha hb
    | true =>
      simp only [d22459, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22460 q = 1) (hb : d169395 q = 1) : d170406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22460, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22460, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150203 q = 1) (hb : d169395 q = 1) : d170407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150203, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150211 q = 1) (hb : d169395 q = 1) : d170433 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150211, d170433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150211, d170433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150212 q = 1) (hb : d169395 q = 1) : d170434 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150212, d170434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150212, d170434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150213 q = 1) (hb : d169395 q = 1) : d170435 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150213, d170435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150213, d170435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49337 (p : Pattern) (ha : d22507 p = 1) (hb : d169395 p = 1) : d170444 p = 1 := by
  have h0 (q : Pattern) (ha : d22500 q = 1) (hb : d116750 q = 1) : d22500 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22501 q = 1) (hb : d169395 q = 1) : d170443 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22501, d169395, d170443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22501, d169395, d170443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15383 q = 1) (hb : d116750 q = 1) : d15383 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22505 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22506 q = 1) (hb : d169395 q = 1) : d15384 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22506, d169395, d15384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22506, d169395, d15384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22507 q = 1) (hb : d169395 q = 1) : d170444 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22507, d170444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22507, d170444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49338 (p : Pattern) (ha : d22514 p = 1) (hb : d169395 p = 1) : d170447 p = 1 := by
  have h0 (q : Pattern) (ha : d17007 q = 1) (hb : d116750 q = 1) : d17007 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22511 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22512 q = 1) (hb : d169395 q = 1) : d170445 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22512, d169395, d170445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22512, d169395, d170445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22505 q = 1) (hb : d116750 q = 1) : d22505 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13493 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22513 q = 1) (hb : d169395 q = 1) : d170446 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22513, d169395, d170446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22513, d169395, d170446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22514 q = 1) (hb : d169395 q = 1) : d170447 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22514, d170447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22514, d170447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49339 (p : Pattern) (ha : d22524 p = 1) (hb : d169395 p = 1) : d170452 p = 1 := by
  have h0 (q : Pattern) (ha : d22521 q = 1) (hb : d116750 q = 1) : d22521 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13493 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22522 q = 1) (hb : d169395 q = 1) : d170451 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22522, d169395, d170451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22522, d169395, d170451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22523 q = 1) (hb : d169395 q = 1) : d22523 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22524 q = 1) (hb : d169395 q = 1) : d170452 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22524, d170452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22524, d170452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49340 (p : Pattern) (ha : d22549 p = 1) (hb : d169395 p = 1) : d170467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22515 q = 1) (hb : d169395 q = 1) : d170448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22515, d170448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49337 q ha hb
    | true =>
      simp only [d22515, d170448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49338 q ha hb
  have h2 (q : Pattern) (ha : d22516 q = 1) (hb : d169395 q = 1) : d170449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22516, d170449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22516, d170449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22517 q = 1) (hb : d169395 q = 1) : d170450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22517, d170450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22517, d170450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22525 q = 1) (hb : d169395 q = 1) : d170453 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22525, d170453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49338 q ha hb
    | true =>
      simp only [d22525, d170453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49339 q ha hb
  have h5 (q : Pattern) (ha : d22526 q = 1) (hb : d169395 q = 1) : d170454 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22526, d170454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22526, d170454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22527 q = 1) (hb : d169395 q = 1) : d170455 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22527, d170455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22527, d170455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22528 q = 1) (hb : d169395 q = 1) : d170456 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22528, d170456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22528, d170456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22535 q = 1) (hb : d169395 q = 1) : d170459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49338 q ha hb
    | true =>
      simp only [d22535, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
  have h9 (q : Pattern) (ha : d22536 q = 1) (hb : d169395 q = 1) : d170460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22537 q = 1) (hb : d169395 q = 1) : d170461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22543 q = 1) (hb : d169395 q = 1) : d22543 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d22544 q = 1) (hb : d169395 q = 1) : d170462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
    | true =>
      simp only [d22544, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22545 q = 1) (hb : d169395 q = 1) : d170463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22546 q = 1) (hb : d169395 q = 1) : d170464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22547 q = 1) (hb : d169395 q = 1) : d170465 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22547, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22548 q = 1) (hb : d169395 q = 1) : d170466 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22548, d170466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22548, d170466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22549 q = 1) (hb : d169395 q = 1) : d170467 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22549, d170467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22549, d170467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro49341 (p : Pattern) (ha : d22554 p = 1) (hb : d169395 p = 1) : d170472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d169395 q = 1) : d170459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49338 q ha hb
    | true =>
      simp only [d22535, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d169395 q = 1) : d170460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d169395 q = 1) : d170461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22543 q = 1) (hb : d169395 q = 1) : d22543 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22544 q = 1) (hb : d169395 q = 1) : d170462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
    | true =>
      simp only [d22544, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22545 q = 1) (hb : d169395 q = 1) : d170463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22546 q = 1) (hb : d169395 q = 1) : d170464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22547 q = 1) (hb : d169395 q = 1) : d170465 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22552 q = 1) (hb : d169395 q = 1) : d170470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22552, d170470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22552, d170470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22553 q = 1) (hb : d169395 q = 1) : d170471 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22553, d170471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22553, d170471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22554 q = 1) (hb : d169395 q = 1) : d170472 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22554, d170472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22554, d170472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro49342 (p : Pattern) (ha : d22560 p = 1) (hb : d169395 p = 1) : d170478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22550 q = 1) (hb : d169395 q = 1) : d170468 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22550, d170468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49340 q ha hb
    | true =>
      simp only [d22550, d170468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22551 q = 1) (hb : d169395 q = 1) : d170469 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22551, d170469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22551, d170469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22555 q = 1) (hb : d169395 q = 1) : d170473 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22555, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49341 q ha hb
    | true =>
      simp only [d22555, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22556 q = 1) (hb : d169395 q = 1) : d170474 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22556, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22556, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22557 q = 1) (hb : d169395 q = 1) : d170475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22557, d170475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22557, d170475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22558 q = 1) (hb : d169395 q = 1) : d170476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22558, d170476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22558, d170476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22559 q = 1) (hb : d169395 q = 1) : d170477 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22559, d170477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22559, d170477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22560 q = 1) (hb : d169395 q = 1) : d170478 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22560, d170478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22560, d170478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49343 (p : Pattern) (ha : d22574 p = 1) (hb : d169395 p = 1) : d170490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22555 q = 1) (hb : d169395 q = 1) : d170473 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22555, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49341 q ha hb
    | true =>
      simp only [d22555, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22556 q = 1) (hb : d169395 q = 1) : d170474 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22556, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22556, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d169395 q = 1) : d170485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49314 q ha hb
    | true =>
      simp only [d22569, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d169395 q = 1) : d170486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22571 q = 1) (hb : d169395 q = 1) : d170487 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22571, d170487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22571, d170487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22572 q = 1) (hb : d169395 q = 1) : d170488 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22572, d170488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22572, d170488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22573 q = 1) (hb : d169395 q = 1) : d170489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22573, d170489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22573, d170489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22574 q = 1) (hb : d169395 q = 1) : d170490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22574, d170490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22574, d170490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49344 (p : Pattern) (ha : d22645 p = 1) (hb : d169395 p = 1) : d170498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d169395 q = 1) : d170459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49338 q ha hb
    | true =>
      simp only [d22535, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d169395 q = 1) : d170460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d169395 q = 1) : d170461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22543 q = 1) (hb : d169395 q = 1) : d22543 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22544 q = 1) (hb : d169395 q = 1) : d170462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
    | true =>
      simp only [d22544, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22545 q = 1) (hb : d169395 q = 1) : d170463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22546 q = 1) (hb : d169395 q = 1) : d170464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22547 q = 1) (hb : d169395 q = 1) : d170465 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22639 q = 1) (hb : d169395 q = 1) : d22639 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22640 q = 1) (hb : d169395 q = 1) : d170493 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22640, d170493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
    | true =>
      simp only [d22640, d170493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22641 q = 1) (hb : d169395 q = 1) : d170494 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22641, d170494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22641, d170494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22642 q = 1) (hb : d169395 q = 1) : d170495 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22642, d170495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22642, d170495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22643 q = 1) (hb : d169395 q = 1) : d170496 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22643, d170496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22643, d170496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22644 q = 1) (hb : d169395 q = 1) : d170497 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22644, d170497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22644, d170497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22645 q = 1) (hb : d169395 q = 1) : d170498 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22645, d170498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22645, d170498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro49345 (p : Pattern) (ha : d22651 p = 1) (hb : d169395 p = 1) : d170504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22646 q = 1) (hb : d169395 q = 1) : d170499 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22646, d170499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49344 q ha hb
    | true =>
      simp only [d22646, d170499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22647 q = 1) (hb : d169395 q = 1) : d170500 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22647, d170500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22647, d170500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22648 q = 1) (hb : d169395 q = 1) : d170501 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22648, d170501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22648, d170501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22649 q = 1) (hb : d169395 q = 1) : d170502 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22649, d170502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22649, d170502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22650 q = 1) (hb : d169395 q = 1) : d170503 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22650, d170503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22650, d170503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22651 q = 1) (hb : d169395 q = 1) : d170504 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22651, d170504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22651, d170504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49346 (p : Pattern) (ha : d150223 p = 1) (hb : d169395 p = 1) : d170510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22575 q = 1) (hb : d169395 q = 1) : d170491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22575, d170491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49342 q ha hb
    | true =>
      simp only [d22575, d170491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49343 q ha hb
  have h2 (q : Pattern) (ha : d150219 q = 1) (hb : d169395 q = 1) : d170492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150219, d170492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150219, d170492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22652 q = 1) (hb : d169395 q = 1) : d170505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22652, d170505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49345 q ha hb
    | true =>
      simp only [d22652, d170505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22653 q = 1) (hb : d169395 q = 1) : d170506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22653, d170506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22653, d170506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150220 q = 1) (hb : d169395 q = 1) : d170507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150220, d170507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150220, d170507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150221 q = 1) (hb : d169395 q = 1) : d170508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150221, d170508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150221, d170508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150222 q = 1) (hb : d169395 q = 1) : d170509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150222, d170509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150222, d170509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150223 q = 1) (hb : d169395 q = 1) : d170510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150223, d170510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150223, d170510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49347 (p : Pattern) (ha : d150229 p = 1) (hb : d169395 p = 1) : d170527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22282 q = 1) (hb : d169395 q = 1) : d170311 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22282, d170311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22282, d170311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49304 q ha hb
  have h2 (q : Pattern) (ha : d22283 q = 1) (hb : d169395 q = 1) : d170312 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22283, d170312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22283, d170312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22292 q = 1) (hb : d169395 q = 1) : d170321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49304 q ha hb
    | true =>
      simp only [d22292, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49307 q ha hb
  have h4 (q : Pattern) (ha : d22293 q = 1) (hb : d169395 q = 1) : d170322 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22293, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22294 q = 1) (hb : d169395 q = 1) : d170323 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d22294, d170323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22294, d170323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150207 q = 1) (hb : d169395 q = 1) : d170411 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150207, d170411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49327 q ha hb
    | true =>
      simp only [d150207, d170411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49335 q ha hb
  have h7 (q : Pattern) (ha : d22483 q = 1) (hb : d169395 q = 1) : d170429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22483, d170429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49310 q ha hb
    | true =>
      simp only [d22483, d170429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49311 q ha hb
  have h8 (q : Pattern) (ha : d150208 q = 1) (hb : d169395 q = 1) : d170430 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150208, d170430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150208, d170430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150209 q = 1) (hb : d169395 q = 1) : d170431 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150209, d170431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150209, d170431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150210 q = 1) (hb : d169395 q = 1) : d170432 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150210, d170432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150210, d170432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150214 q = 1) (hb : d169395 q = 1) : d170436 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150214, d170436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150214, d170436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49336 q ha hb
  have h12 (q : Pattern) (ha : d22492 q = 1) (hb : d169395 q = 1) : d170438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22492, d170438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22492, d170438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49312 q ha hb
  have h13 (q : Pattern) (ha : d150215 q = 1) (hb : d169395 q = 1) : d170439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150215, d170439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150215, d170439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150216 q = 1) (hb : d169395 q = 1) : d170440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150216, d170440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150216, d170440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150217 q = 1) (hb : d169395 q = 1) : d170441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150217, d170441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150217, d170441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150218 q = 1) (hb : d169395 q = 1) : d170442 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150218, d170442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150218, d170442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150224 q = 1) (hb : d169395 q = 1) : d170511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150224, d170511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150224, d170511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49346 q ha hb
  have h18 (q : Pattern) (ha : d22669 q = 1) (hb : d169395 q = 1) : d170522 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22669, d170522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22669, d170522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49316 q ha hb
  have h19 (q : Pattern) (ha : d150225 q = 1) (hb : d169395 q = 1) : d170523 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150225, d170523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150225, d170523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150226 q = 1) (hb : d169395 q = 1) : d170524 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150226, d170524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150226, d170524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150227 q = 1) (hb : d169395 q = 1) : d170525 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150227, d170525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150227, d170525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150228 q = 1) (hb : d169395 q = 1) : d170526 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150228, d170526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150228, d170526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150229 q = 1) (hb : d169395 q = 1) : d170527 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150229, d170527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150229, d170527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49348 (p : Pattern) (ha : d150235 p = 1) (hb : d169395 p = 1) : d170533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150230 q = 1) (hb : d169395 q = 1) : d170528 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150230, d170528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150230, d170528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49347 q ha hb
  have h2 (q : Pattern) (ha : d150231 q = 1) (hb : d169395 q = 1) : d170529 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150231, d170529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150231, d170529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150232 q = 1) (hb : d169395 q = 1) : d170530 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150232, d170530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150232, d170530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150233 q = 1) (hb : d169395 q = 1) : d170531 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150233, d170531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150233, d170531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150234 q = 1) (hb : d169395 q = 1) : d170532 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150234, d170532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150234, d170532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150235 q = 1) (hb : d169395 q = 1) : d170533 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150235, d170533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150235, d170533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49349 (p : Pattern) (ha : d22686 p = 1) (hb : d169395 p = 1) : d170539 p = 1 := by
  have h0 (q : Pattern) (ha : d17226 q = 1) (hb : d116750 q = 1) : d17226 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22685 q = 1) (hb : d169395 q = 1) : d170538 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22685, d169395, d170538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22685, d169395, d170538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13676 q = 1) (hb : d116750 q = 1) : d13676 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13681 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13682 q = 1) (hb : d169395 q = 1) : d15545 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d169395, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13682, d169395, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22686 q = 1) (hb : d169395 q = 1) : d170539 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22686, d170539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22686, d170539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49350 (p : Pattern) (ha : d22694 p = 1) (hb : d169395 p = 1) : d170541 p = 1 := by
  have h0 (q : Pattern) (ha : d17154 q = 1) (hb : d116750 q = 1) : d17154 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22692 q = 1) (hb : d169395 q = 1) : d170540 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22692, d169395, d170540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22692, d169395, d170540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22693 q = 1) (hb : d169395 q = 1) : d22693 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22694 q = 1) (hb : d169395 q = 1) : d170541 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22694, d170541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22694, d170541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49351 (p : Pattern) (ha : d22716 p = 1) (hb : d169395 p = 1) : d170554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d169395 q = 1) : d170542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49349 q ha hb
    | true =>
      simp only [d22695, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d169395 q = 1) : d170543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d169395 q = 1) : d170544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22704 q = 1) (hb : d169395 q = 1) : d22704 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22705 q = 1) (hb : d169395 q = 1) : d170545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
    | true =>
      simp only [d22705, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22706 q = 1) (hb : d169395 q = 1) : d170546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22707 q = 1) (hb : d169395 q = 1) : d170547 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22708 q = 1) (hb : d169395 q = 1) : d170548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22710 q = 1) (hb : d169395 q = 1) : d22710 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22711 q = 1) (hb : d169395 q = 1) : d170549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22711, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
    | true =>
      simp only [d22711, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22712 q = 1) (hb : d169395 q = 1) : d170550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22712, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22712, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22713 q = 1) (hb : d169395 q = 1) : d170551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22713, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22713, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22714 q = 1) (hb : d169395 q = 1) : d170552 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22714, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22714, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22715 q = 1) (hb : d169395 q = 1) : d170553 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22715, d170553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22715, d170553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22716 q = 1) (hb : d169395 q = 1) : d170554 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22716, d170554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22716, d170554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro49352 (p : Pattern) (ha : d22720 p = 1) (hb : d169395 p = 1) : d170558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22710 q = 1) (hb : d169395 q = 1) : d22710 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22711 q = 1) (hb : d169395 q = 1) : d170549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22711, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
    | true =>
      simp only [d22711, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22712 q = 1) (hb : d169395 q = 1) : d170550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22712, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22712, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22713 q = 1) (hb : d169395 q = 1) : d170551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22713, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22713, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22714 q = 1) (hb : d169395 q = 1) : d170552 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22714, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22714, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22719 q = 1) (hb : d169395 q = 1) : d170557 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22719, d170557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22719, d170557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22720 q = 1) (hb : d169395 q = 1) : d170558 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22720, d170558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22720, d170558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49353 (p : Pattern) (ha : d22726 p = 1) (hb : d169395 p = 1) : d170564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49351 q ha hb
    | true =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d169395 q = 1) : d170562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22725 q = 1) (hb : d169395 q = 1) : d170563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22725, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22725, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22726 q = 1) (hb : d169395 q = 1) : d170564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22726, d170564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22726, d170564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49354 (p : Pattern) (ha : d22730 p = 1) (hb : d169395 p = 1) : d170568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d169395 q = 1) : d170566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22729 q = 1) (hb : d169395 q = 1) : d170567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22729, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22729, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22730 q = 1) (hb : d169395 q = 1) : d170568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22730, d170568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22730, d170568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49355 (p : Pattern) (ha : d22736 p = 1) (hb : d169395 p = 1) : d170574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22731 q = 1) (hb : d169395 q = 1) : d170569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49353 q ha hb
    | true =>
      simp only [d22731, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49354 q ha hb
  have h2 (q : Pattern) (ha : d22732 q = 1) (hb : d169395 q = 1) : d170570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22732, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22733 q = 1) (hb : d169395 q = 1) : d170571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22733, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22734 q = 1) (hb : d169395 q = 1) : d170572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22734, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22735 q = 1) (hb : d169395 q = 1) : d170573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22736 q = 1) (hb : d169395 q = 1) : d170574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22736, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22736, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49356 (p : Pattern) (ha : d22739 p = 1) (hb : d169395 p = 1) : d170577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49351 q ha hb
    | true =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d169395 q = 1) : d170562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22725 q = 1) (hb : d169395 q = 1) : d170563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22725, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22725, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22739 q = 1) (hb : d169395 q = 1) : d170577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22739, d170577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22739, d170577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49357 (p : Pattern) (ha : d22740 p = 1) (hb : d169395 p = 1) : d170578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d169395 q = 1) : d170566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22729 q = 1) (hb : d169395 q = 1) : d170567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22729, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22729, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22740 q = 1) (hb : d169395 q = 1) : d170578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22740, d170578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22740, d170578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49358 (p : Pattern) (ha : d22746 p = 1) (hb : d169395 p = 1) : d170584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22731 q = 1) (hb : d169395 q = 1) : d170569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49353 q ha hb
    | true =>
      simp only [d22731, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49354 q ha hb
  have h2 (q : Pattern) (ha : d22732 q = 1) (hb : d169395 q = 1) : d170570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22732, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22733 q = 1) (hb : d169395 q = 1) : d170571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22733, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22734 q = 1) (hb : d169395 q = 1) : d170572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22734, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22735 q = 1) (hb : d169395 q = 1) : d170573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22741 q = 1) (hb : d169395 q = 1) : d170579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49356 q ha hb
    | true =>
      simp only [d22741, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49357 q ha hb
  have h7 (q : Pattern) (ha : d22742 q = 1) (hb : d169395 q = 1) : d170580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22743 q = 1) (hb : d169395 q = 1) : d170581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22743, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22744 q = 1) (hb : d169395 q = 1) : d170582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22745 q = 1) (hb : d169395 q = 1) : d170583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22746 q = 1) (hb : d169395 q = 1) : d170584 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22746, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22746, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49359 (p : Pattern) (ha : d22783 p = 1) (hb : d169395 p = 1) : d170619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d169395 q = 1) : d170542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49349 q ha hb
    | true =>
      simp only [d22695, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d169395 q = 1) : d170543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d169395 q = 1) : d170544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22704 q = 1) (hb : d169395 q = 1) : d22704 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22705 q = 1) (hb : d169395 q = 1) : d170545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
    | true =>
      simp only [d22705, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22706 q = 1) (hb : d169395 q = 1) : d170546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22707 q = 1) (hb : d169395 q = 1) : d170547 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22708 q = 1) (hb : d169395 q = 1) : d170548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22781 q = 1) (hb : d169395 q = 1) : d170617 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22781, d170617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22781, d170617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22782 q = 1) (hb : d169395 q = 1) : d170618 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22782, d170618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22782, d170618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22783 q = 1) (hb : d169395 q = 1) : d170619 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22783, d170619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22783, d170619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro49360 (p : Pattern) (ha : d22793 p = 1) (hb : d169395 p = 1) : d170629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22784 q = 1) (hb : d169395 q = 1) : d170620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49359 q ha hb
    | true =>
      simp only [d22784, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22785 q = 1) (hb : d169395 q = 1) : d170621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22790 q = 1) (hb : d169395 q = 1) : d170626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22790, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22790, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22791 q = 1) (hb : d169395 q = 1) : d170627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22791, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22791, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22792 q = 1) (hb : d169395 q = 1) : d170628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22792, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22792, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22793 q = 1) (hb : d169395 q = 1) : d170629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22793, d170629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22793, d170629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49361 (p : Pattern) (ha : d22909 p = 1) (hb : d169395 p = 1) : d170683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22899 q = 1) (hb : d169395 q = 1) : d170673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22899, d170673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49360 q ha hb
    | true =>
      simp only [d22899, d170673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49354 q ha hb
  have h2 (q : Pattern) (ha : d22900 q = 1) (hb : d169395 q = 1) : d170674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22900, d170674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22900, d170674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22901 q = 1) (hb : d169395 q = 1) : d170675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22901, d170675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22901, d170675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22902 q = 1) (hb : d169395 q = 1) : d170676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22902, d170676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22902, d170676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22903 q = 1) (hb : d169395 q = 1) : d170677 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22903, d170677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22903, d170677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22904 q = 1) (hb : d169395 q = 1) : d170678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22904, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49354 q ha hb
    | true =>
      simp only [d22904, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22905 q = 1) (hb : d169395 q = 1) : d170679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22905, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22905, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22906 q = 1) (hb : d169395 q = 1) : d170680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22906, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22906, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22907 q = 1) (hb : d169395 q = 1) : d170681 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22907, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22907, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22908 q = 1) (hb : d169395 q = 1) : d170682 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22908, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22908, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22909 q = 1) (hb : d169395 q = 1) : d170683 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22909, d170683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22909, d170683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49362 (p : Pattern) (ha : d22915 p = 1) (hb : d169395 p = 1) : d170689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22904 q = 1) (hb : d169395 q = 1) : d170678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22904, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49354 q ha hb
    | true =>
      simp only [d22904, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22905 q = 1) (hb : d169395 q = 1) : d170679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22905, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22905, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22906 q = 1) (hb : d169395 q = 1) : d170680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22906, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22906, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22907 q = 1) (hb : d169395 q = 1) : d170681 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22907, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22907, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22908 q = 1) (hb : d169395 q = 1) : d170682 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22908, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22908, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22910 q = 1) (hb : d169395 q = 1) : d170684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22910, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49357 q ha hb
    | true =>
      simp only [d22910, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22911 q = 1) (hb : d169395 q = 1) : d170685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22911, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22911, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22912 q = 1) (hb : d169395 q = 1) : d170686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22912, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22912, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22913 q = 1) (hb : d169395 q = 1) : d170687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22913, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22913, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22914 q = 1) (hb : d169395 q = 1) : d170688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22914, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22914, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22915 q = 1) (hb : d169395 q = 1) : d170689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22915, d170689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22915, d170689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49363 (p : Pattern) (ha : d22924 p = 1) (hb : d169395 p = 1) : d170698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22910 q = 1) (hb : d169395 q = 1) : d170684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22910, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49357 q ha hb
    | true =>
      simp only [d22910, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22911 q = 1) (hb : d169395 q = 1) : d170685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22911, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22911, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22912 q = 1) (hb : d169395 q = 1) : d170686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22912, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22912, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22913 q = 1) (hb : d169395 q = 1) : d170687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22913, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22913, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22914 q = 1) (hb : d169395 q = 1) : d170688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22914, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22914, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22924 q = 1) (hb : d169395 q = 1) : d170698 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22924, d170698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22924, d170698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49364 (p : Pattern) (ha : d22948 p = 1) (hb : d169395 p = 1) : d170715 p = 1 := by
  have h0 (q : Pattern) (ha : d17379 q = 1) (hb : d116750 q = 1) : d17379 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22946 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22947 q = 1) (hb : d169395 q = 1) : d170714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22947, d169395, d170714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22947, d169395, d170714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22937 q = 1) (hb : d169395 q = 1) : d22937 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22948 q = 1) (hb : d169395 q = 1) : d170715 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22948, d170715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22948, d170715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49365 (p : Pattern) (ha : d22982 p = 1) (hb : d169395 p = 1) : d170741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22976 q = 1) (hb : d169395 q = 1) : d22976 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22977 q = 1) (hb : d169395 q = 1) : d170736 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
    | true =>
      simp only [d22977, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22978 q = 1) (hb : d169395 q = 1) : d170737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22979 q = 1) (hb : d169395 q = 1) : d170738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22980 q = 1) (hb : d169395 q = 1) : d170739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22980, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22981 q = 1) (hb : d169395 q = 1) : d170740 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22981, d170740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22981, d170740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22982 q = 1) (hb : d169395 q = 1) : d170741 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22982, d170741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22982, d170741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49366 (p : Pattern) (ha : d23068 p = 1) (hb : d169395 p = 1) : d170772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22983 q = 1) (hb : d169395 q = 1) : d170742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49365 q ha hb
    | true =>
      simp only [d22983, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22984 q = 1) (hb : d169395 q = 1) : d170743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23065 q = 1) (hb : d169395 q = 1) : d170769 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23065, d170769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23065, d170769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23066 q = 1) (hb : d169395 q = 1) : d170770 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23066, d170770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23066, d170770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23067 q = 1) (hb : d169395 q = 1) : d170771 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23067, d170771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23067, d170771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23068 q = 1) (hb : d169395 q = 1) : d170772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23068, d170772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23068, d170772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49367 (p : Pattern) (ha : d23074 p = 1) (hb : d169395 p = 1) : d170778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23069 q = 1) (hb : d169395 q = 1) : d170773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23069, d170773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49366 q ha hb
    | true =>
      simp only [d23069, d170773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23070 q = 1) (hb : d169395 q = 1) : d170774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23070, d170774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23070, d170774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23071 q = 1) (hb : d169395 q = 1) : d170775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23071, d170775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23071, d170775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23072 q = 1) (hb : d169395 q = 1) : d170776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23072, d170776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23072, d170776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23073 q = 1) (hb : d169395 q = 1) : d170777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23073, d170777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23073, d170777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23074 q = 1) (hb : d169395 q = 1) : d170778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23074, d170778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23074, d170778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49368 (p : Pattern) (ha : d22751 p = 1) (hb : d169395 p = 1) : d170589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49351 q ha hb
    | true =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d169395 q = 1) : d170562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22750 q = 1) (hb : d169395 q = 1) : d170588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22750, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22750, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22751 q = 1) (hb : d169395 q = 1) : d170589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22751, d170589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22751, d170589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49369 (p : Pattern) (ha : d22753 p = 1) (hb : d169395 p = 1) : d170591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d169395 q = 1) : d170566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22752 q = 1) (hb : d169395 q = 1) : d170590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22752, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22752, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22753 q = 1) (hb : d169395 q = 1) : d170591 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22753, d170591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22753, d170591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49370 (p : Pattern) (ha : d22760 p = 1) (hb : d169395 p = 1) : d170598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49351 q ha hb
    | true =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22758 q = 1) (hb : d169395 q = 1) : d170596 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22758, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22758, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22759 q = 1) (hb : d169395 q = 1) : d170597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22759, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22759, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22760 q = 1) (hb : d169395 q = 1) : d170598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22760, d170598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22760, d170598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49371 (p : Pattern) (ha : d22763 p = 1) (hb : d169395 p = 1) : d170601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22761 q = 1) (hb : d169395 q = 1) : d170599 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22761, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22761, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22762 q = 1) (hb : d169395 q = 1) : d170600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22762, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22762, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22763 q = 1) (hb : d169395 q = 1) : d170601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22763, d170601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22763, d170601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49372 (p : Pattern) (ha : d22768 p = 1) (hb : d169395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17226 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22767 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22767, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22767, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13676 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17228 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17228, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17228, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d22768 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro49373 (p : Pattern) (ha : d22772 p = 1) (hb : d169395 p = 1) : d170608 p = 1 := by
  have h0 (q : Pattern) (ha : d13676 q = 1) (hb : d116750 q = 1) : d13676 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13681 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13682 q = 1) (hb : d169395 q = 1) : d15545 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d169395, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13682, d169395, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22693 q = 1) (hb : d169395 q = 1) : d22693 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22772 q = 1) (hb : d169395 q = 1) : d170608 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22772, d170608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22772, d170608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49374 (p : Pattern) (ha : d22778 p = 1) (hb : d169395 p = 1) : d170614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22769 q = 1) (hb : d169395 q = 1) : d170605 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22769, d170605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49372 q ha hb
    | true =>
      simp only [d22769, d170605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49349 q ha hb
  have h2 (q : Pattern) (ha : d22770 q = 1) (hb : d169395 q = 1) : d170606 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22770, d170606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22770, d170606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22771 q = 1) (hb : d169395 q = 1) : d170607 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22771, d170607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22771, d170607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22773 q = 1) (hb : d169395 q = 1) : d170609 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22773, d170609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49349 q ha hb
    | true =>
      simp only [d22773, d170609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49373 q ha hb
  have h5 (q : Pattern) (ha : d22774 q = 1) (hb : d169395 q = 1) : d170610 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22774, d170610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22774, d170610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22775 q = 1) (hb : d169395 q = 1) : d170611 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22775, d170611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22775, d170611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22776 q = 1) (hb : d169395 q = 1) : d170612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22776, d170612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22776, d170612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22695 q = 1) (hb : d169395 q = 1) : d170542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49349 q ha hb
    | true =>
      simp only [d22695, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
  have h9 (q : Pattern) (ha : d22696 q = 1) (hb : d169395 q = 1) : d170543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22697 q = 1) (hb : d169395 q = 1) : d170544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22704 q = 1) (hb : d169395 q = 1) : d22704 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d22705 q = 1) (hb : d169395 q = 1) : d170545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
    | true =>
      simp only [d22705, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22706 q = 1) (hb : d169395 q = 1) : d170546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22707 q = 1) (hb : d169395 q = 1) : d170547 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22708 q = 1) (hb : d169395 q = 1) : d170548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22708, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22777 q = 1) (hb : d169395 q = 1) : d170613 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22777, d170613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22777, d170613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22778 q = 1) (hb : d169395 q = 1) : d170614 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22778, d170614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22778, d170614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro49375 (p : Pattern) (ha : d22789 p = 1) (hb : d169395 p = 1) : d170625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22779 q = 1) (hb : d169395 q = 1) : d170615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22779, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49374 q ha hb
    | true =>
      simp only [d22779, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22780 q = 1) (hb : d169395 q = 1) : d170616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22780, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22780, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22784 q = 1) (hb : d169395 q = 1) : d170620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49359 q ha hb
    | true =>
      simp only [d22784, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22785 q = 1) (hb : d169395 q = 1) : d170621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22786 q = 1) (hb : d169395 q = 1) : d170622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22786, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22786, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22787 q = 1) (hb : d169395 q = 1) : d170623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22787, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22787, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22788 q = 1) (hb : d169395 q = 1) : d170624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22788, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22788, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22789 q = 1) (hb : d169395 q = 1) : d170625 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22789, d170625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22789, d170625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49376 (p : Pattern) (ha : d22860 p = 1) (hb : d169395 p = 1) : d170637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d169395 q = 1) : d170542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49349 q ha hb
    | true =>
      simp only [d22695, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d169395 q = 1) : d170543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d169395 q = 1) : d170544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22704 q = 1) (hb : d169395 q = 1) : d22704 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22705 q = 1) (hb : d169395 q = 1) : d170545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
    | true =>
      simp only [d22705, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22706 q = 1) (hb : d169395 q = 1) : d170546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22707 q = 1) (hb : d169395 q = 1) : d170547 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22708 q = 1) (hb : d169395 q = 1) : d170548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22854 q = 1) (hb : d169395 q = 1) : d22854 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22855 q = 1) (hb : d169395 q = 1) : d170632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22855, d170632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49350 q ha hb
    | true =>
      simp only [d22855, d170632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22856 q = 1) (hb : d169395 q = 1) : d170633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22856, d170633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22856, d170633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22857 q = 1) (hb : d169395 q = 1) : d170634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22857, d170634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22857, d170634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22858 q = 1) (hb : d169395 q = 1) : d170635 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22858, d170635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22858, d170635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22859 q = 1) (hb : d169395 q = 1) : d170636 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22859, d170636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22859, d170636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22860 q = 1) (hb : d169395 q = 1) : d170637 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22860, d170637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22860, d170637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro49377 (p : Pattern) (ha : d22866 p = 1) (hb : d169395 p = 1) : d170643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22861 q = 1) (hb : d169395 q = 1) : d170638 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22861, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49376 q ha hb
    | true =>
      simp only [d22861, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22862 q = 1) (hb : d169395 q = 1) : d170639 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22862, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22862, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22863 q = 1) (hb : d169395 q = 1) : d170640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22863, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22863, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22864 q = 1) (hb : d169395 q = 1) : d170641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22864, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22864, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22865 q = 1) (hb : d169395 q = 1) : d170642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22865, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22865, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22866 q = 1) (hb : d169395 q = 1) : d170643 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22866, d170643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22866, d170643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49378 (p : Pattern) (ha : d150244 p = 1) (hb : d169395 p = 1) : d170649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22754 q = 1) (hb : d169395 q = 1) : d170592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22754, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49368 q ha hb
    | true =>
      simp only [d22754, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49369 q ha hb
  have h2 (q : Pattern) (ha : d22755 q = 1) (hb : d169395 q = 1) : d170593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22755, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22755, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22756 q = 1) (hb : d169395 q = 1) : d170594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22756, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22756, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22757 q = 1) (hb : d169395 q = 1) : d170595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22757, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22757, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22764 q = 1) (hb : d169395 q = 1) : d170602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22764, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49370 q ha hb
    | true =>
      simp only [d22764, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49371 q ha hb
  have h6 (q : Pattern) (ha : d22765 q = 1) (hb : d169395 q = 1) : d170603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22765, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22765, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22766 q = 1) (hb : d169395 q = 1) : d170604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22766, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22766, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22794 q = 1) (hb : d169395 q = 1) : d170630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22794, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49375 q ha hb
    | true =>
      simp only [d22794, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49360 q ha hb
  have h9 (q : Pattern) (ha : d150240 q = 1) (hb : d169395 q = 1) : d170631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150240, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22867 q = 1) (hb : d169395 q = 1) : d170644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22867, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49377 q ha hb
    | true =>
      simp only [d22867, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22868 q = 1) (hb : d169395 q = 1) : d170645 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22868, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22868, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150241 q = 1) (hb : d169395 q = 1) : d170646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150241, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150242 q = 1) (hb : d169395 q = 1) : d170647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150242, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150243 q = 1) (hb : d169395 q = 1) : d170648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150243, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150244 q = 1) (hb : d169395 q = 1) : d170649 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150244, d170649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150244, d170649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49379 (p : Pattern) (ha : d22873 p = 1) (hb : d169395 p = 1) : d170650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49351 q ha hb
    | true =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d169395 q = 1) : d170562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22750 q = 1) (hb : d169395 q = 1) : d170588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22750, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22750, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22873 q = 1) (hb : d169395 q = 1) : d170650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22873, d170650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22873, d170650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49380 (p : Pattern) (ha : d22874 p = 1) (hb : d169395 p = 1) : d170651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d169395 q = 1) : d170566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22752 q = 1) (hb : d169395 q = 1) : d170590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22752, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22752, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22874 q = 1) (hb : d169395 q = 1) : d170651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22874, d170651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22874, d170651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49381 (p : Pattern) (ha : d22879 p = 1) (hb : d169395 p = 1) : d170656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49351 q ha hb
    | true =>
      simp only [d22717, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22758 q = 1) (hb : d169395 q = 1) : d170596 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22758, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22758, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22759 q = 1) (hb : d169395 q = 1) : d170597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22759, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22759, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22879 q = 1) (hb : d169395 q = 1) : d170656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22879, d170656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22879, d170656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49382 (p : Pattern) (ha : d22880 p = 1) (hb : d169395 p = 1) : d170657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22761 q = 1) (hb : d169395 q = 1) : d170599 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22761, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22761, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22762 q = 1) (hb : d169395 q = 1) : d170600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22762, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22762, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22880 q = 1) (hb : d169395 q = 1) : d170657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22880, d170657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22880, d170657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49383 (p : Pattern) (ha : d22884 p = 1) (hb : d169395 p = 1) : d170661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22779 q = 1) (hb : d169395 q = 1) : d170615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22779, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49374 q ha hb
    | true =>
      simp only [d22779, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22780 q = 1) (hb : d169395 q = 1) : d170616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22780, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22780, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22784 q = 1) (hb : d169395 q = 1) : d170620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49359 q ha hb
    | true =>
      simp only [d22784, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22785 q = 1) (hb : d169395 q = 1) : d170621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22786 q = 1) (hb : d169395 q = 1) : d170622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22786, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22786, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22787 q = 1) (hb : d169395 q = 1) : d170623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22787, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22787, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22788 q = 1) (hb : d169395 q = 1) : d170624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22788, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22788, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22884 q = 1) (hb : d169395 q = 1) : d170661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22884, d170661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22884, d170661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49384 (p : Pattern) (ha : d22885 p = 1) (hb : d169395 p = 1) : d170662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22784 q = 1) (hb : d169395 q = 1) : d170620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49359 q ha hb
    | true =>
      simp only [d22784, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22785 q = 1) (hb : d169395 q = 1) : d170621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49352 q ha hb
    | true =>
      simp only [d22721, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22790 q = 1) (hb : d169395 q = 1) : d170626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22790, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22790, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22791 q = 1) (hb : d169395 q = 1) : d170627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22791, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22791, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22792 q = 1) (hb : d169395 q = 1) : d170628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22792, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22792, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22885 q = 1) (hb : d169395 q = 1) : d170662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22885, d170662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22885, d170662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49385 (p : Pattern) (ha : d22891 p = 1) (hb : d169395 p = 1) : d170665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22861 q = 1) (hb : d169395 q = 1) : d170638 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22861, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49376 q ha hb
    | true =>
      simp only [d22861, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22862 q = 1) (hb : d169395 q = 1) : d170639 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22862, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22862, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22863 q = 1) (hb : d169395 q = 1) : d170640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22863, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22863, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22864 q = 1) (hb : d169395 q = 1) : d170641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22864, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22864, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22865 q = 1) (hb : d169395 q = 1) : d170642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22865, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22865, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22891 q = 1) (hb : d169395 q = 1) : d170665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22891, d170665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22891, d170665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49386 (p : Pattern) (ha : d150249 p = 1) (hb : d169395 p = 1) : d170671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22754 q = 1) (hb : d169395 q = 1) : d170592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22754, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49368 q ha hb
    | true =>
      simp only [d22754, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49369 q ha hb
  have h2 (q : Pattern) (ha : d22755 q = 1) (hb : d169395 q = 1) : d170593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22755, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22755, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22756 q = 1) (hb : d169395 q = 1) : d170594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22756, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22756, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22757 q = 1) (hb : d169395 q = 1) : d170595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22757, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22757, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22764 q = 1) (hb : d169395 q = 1) : d170602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22764, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49370 q ha hb
    | true =>
      simp only [d22764, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49371 q ha hb
  have h6 (q : Pattern) (ha : d22765 q = 1) (hb : d169395 q = 1) : d170603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22765, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22765, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22766 q = 1) (hb : d169395 q = 1) : d170604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22766, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22766, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22794 q = 1) (hb : d169395 q = 1) : d170630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22794, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49375 q ha hb
    | true =>
      simp only [d22794, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49360 q ha hb
  have h9 (q : Pattern) (ha : d150240 q = 1) (hb : d169395 q = 1) : d170631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150240, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22867 q = 1) (hb : d169395 q = 1) : d170644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22867, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49377 q ha hb
    | true =>
      simp only [d22867, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22868 q = 1) (hb : d169395 q = 1) : d170645 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22868, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22868, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150241 q = 1) (hb : d169395 q = 1) : d170646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150241, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150242 q = 1) (hb : d169395 q = 1) : d170647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150242, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150243 q = 1) (hb : d169395 q = 1) : d170648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150243, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22875 q = 1) (hb : d169395 q = 1) : d170652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22875, d170652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49379 q ha hb
    | true =>
      simp only [d22875, d170652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49380 q ha hb
  have h16 (q : Pattern) (ha : d22876 q = 1) (hb : d169395 q = 1) : d170653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22876, d170653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22876, d170653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22877 q = 1) (hb : d169395 q = 1) : d170654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22877, d170654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22877, d170654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22878 q = 1) (hb : d169395 q = 1) : d170655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22878, d170655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22878, d170655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22881 q = 1) (hb : d169395 q = 1) : d170658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22881, d170658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49381 q ha hb
    | true =>
      simp only [d22881, d170658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49382 q ha hb
  have h20 (q : Pattern) (ha : d22882 q = 1) (hb : d169395 q = 1) : d170659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22882, d170659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22882, d170659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d22883 q = 1) (hb : d169395 q = 1) : d170660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22883, d170660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22883, d170660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22886 q = 1) (hb : d169395 q = 1) : d170663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22886, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49383 q ha hb
    | true =>
      simp only [d22886, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49384 q ha hb
  have h23 (q : Pattern) (ha : d150245 q = 1) (hb : d169395 q = 1) : d170664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150245, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d22892 q = 1) (hb : d169395 q = 1) : d170666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22892, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49385 q ha hb
    | true =>
      simp only [d22892, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d22893 q = 1) (hb : d169395 q = 1) : d170667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22893, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22893, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150246 q = 1) (hb : d169395 q = 1) : d170668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150246, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150247 q = 1) (hb : d169395 q = 1) : d170669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150247, d170669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150247, d170669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150248 q = 1) (hb : d169395 q = 1) : d170670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150248, d170670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150248, d170670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150249 q = 1) (hb : d169395 q = 1) : d170671 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150249, d170671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150249, d170671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro49387 (p : Pattern) (ha : d150256 p = 1) (hb : d169395 p = 1) : d170696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22886 q = 1) (hb : d169395 q = 1) : d170663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22886, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49383 q ha hb
    | true =>
      simp only [d22886, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49384 q ha hb
  have h2 (q : Pattern) (ha : d150245 q = 1) (hb : d169395 q = 1) : d170664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150245, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22892 q = 1) (hb : d169395 q = 1) : d170666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22892, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49385 q ha hb
    | true =>
      simp only [d22892, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22893 q = 1) (hb : d169395 q = 1) : d170667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22893, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22893, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150246 q = 1) (hb : d169395 q = 1) : d170668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150246, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150254 q = 1) (hb : d169395 q = 1) : d170694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150254, d170694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150254, d170694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150255 q = 1) (hb : d169395 q = 1) : d170695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150255, d170695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150255, d170695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150256 q = 1) (hb : d169395 q = 1) : d170696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150256, d170696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150256, d170696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49388 (p : Pattern) (ha : d22931 p = 1) (hb : d169395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17372 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22930 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22930, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22930, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13816 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17374 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17374, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17374, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d22931 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro49389 (p : Pattern) (ha : d22933 p = 1) (hb : d169395 p = 1) : d170705 p = 1 := by
  have h0 (q : Pattern) (ha : d17372 q = 1) (hb : d116750 q = 1) : d17372 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17379 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22932 q = 1) (hb : d169395 q = 1) : d170704 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22932, d169395, d170704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22932, d169395, d170704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13816 q = 1) (hb : d116750 q = 1) : d13816 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13820 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13821 q = 1) (hb : d169395 q = 1) : d15770 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d169395, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13821, d169395, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22933 q = 1) (hb : d169395 q = 1) : d170705 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22933, d170705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22933, d170705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49390 (p : Pattern) (ha : d22938 p = 1) (hb : d169395 p = 1) : d170709 p = 1 := by
  have h0 (q : Pattern) (ha : d13816 q = 1) (hb : d116750 q = 1) : d13816 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13820 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13821 q = 1) (hb : d169395 q = 1) : d15770 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d169395, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13821, d169395, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22937 q = 1) (hb : d169395 q = 1) : d22937 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22938 q = 1) (hb : d169395 q = 1) : d170709 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22938, d170709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22938, d170709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49391 (p : Pattern) (ha : d22963 p = 1) (hb : d169395 p = 1) : d170724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22934 q = 1) (hb : d169395 q = 1) : d170706 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22934, d170706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49388 q ha hb
    | true =>
      simp only [d22934, d170706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49389 q ha hb
  have h2 (q : Pattern) (ha : d22935 q = 1) (hb : d169395 q = 1) : d170707 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22935, d170707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22935, d170707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22936 q = 1) (hb : d169395 q = 1) : d170708 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22936, d170708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22936, d170708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22939 q = 1) (hb : d169395 q = 1) : d170710 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22939, d170710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49389 q ha hb
    | true =>
      simp only [d22939, d170710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49390 q ha hb
  have h5 (q : Pattern) (ha : d22940 q = 1) (hb : d169395 q = 1) : d170711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22940, d170711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22940, d170711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22941 q = 1) (hb : d169395 q = 1) : d170712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22941, d170712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22941, d170712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22942 q = 1) (hb : d169395 q = 1) : d170713 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22942, d170713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22942, d170713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22949 q = 1) (hb : d169395 q = 1) : d170716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49389 q ha hb
    | true =>
      simp only [d22949, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
  have h9 (q : Pattern) (ha : d22950 q = 1) (hb : d169395 q = 1) : d170717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22951 q = 1) (hb : d169395 q = 1) : d170718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22957 q = 1) (hb : d169395 q = 1) : d22957 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d22958 q = 1) (hb : d169395 q = 1) : d170719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
    | true =>
      simp only [d22958, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22959 q = 1) (hb : d169395 q = 1) : d170720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22960 q = 1) (hb : d169395 q = 1) : d170721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22961 q = 1) (hb : d169395 q = 1) : d170722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22961, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22962 q = 1) (hb : d169395 q = 1) : d170723 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22962, d170723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22962, d170723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22963 q = 1) (hb : d169395 q = 1) : d170724 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22963, d170724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22963, d170724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro49392 (p : Pattern) (ha : d22968 p = 1) (hb : d169395 p = 1) : d170729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d169395 q = 1) : d170716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49389 q ha hb
    | true =>
      simp only [d22949, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d169395 q = 1) : d170717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d169395 q = 1) : d170718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22957 q = 1) (hb : d169395 q = 1) : d22957 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22958 q = 1) (hb : d169395 q = 1) : d170719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
    | true =>
      simp only [d22958, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22959 q = 1) (hb : d169395 q = 1) : d170720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22960 q = 1) (hb : d169395 q = 1) : d170721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22961 q = 1) (hb : d169395 q = 1) : d170722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22966 q = 1) (hb : d169395 q = 1) : d170727 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22966, d170727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22966, d170727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22967 q = 1) (hb : d169395 q = 1) : d170728 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22967, d170728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22967, d170728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22968 q = 1) (hb : d169395 q = 1) : d170729 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22968, d170729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22968, d170729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro49393 (p : Pattern) (ha : d22974 p = 1) (hb : d169395 p = 1) : d170735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22964 q = 1) (hb : d169395 q = 1) : d170725 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22964, d170725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49391 q ha hb
    | true =>
      simp only [d22964, d170725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22965 q = 1) (hb : d169395 q = 1) : d170726 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22965, d170726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22965, d170726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22969 q = 1) (hb : d169395 q = 1) : d170730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22969, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49392 q ha hb
    | true =>
      simp only [d22969, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22970 q = 1) (hb : d169395 q = 1) : d170731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22970, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22970, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22971 q = 1) (hb : d169395 q = 1) : d170732 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22971, d170732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22971, d170732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22972 q = 1) (hb : d169395 q = 1) : d170733 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22972, d170733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22972, d170733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22973 q = 1) (hb : d169395 q = 1) : d170734 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22973, d170734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22973, d170734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22974 q = 1) (hb : d169395 q = 1) : d170735 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22974, d170735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22974, d170735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49394 (p : Pattern) (ha : d22988 p = 1) (hb : d169395 p = 1) : d170747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22969 q = 1) (hb : d169395 q = 1) : d170730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22969, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49392 q ha hb
    | true =>
      simp only [d22969, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22970 q = 1) (hb : d169395 q = 1) : d170731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22970, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22970, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d169395 q = 1) : d170742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49365 q ha hb
    | true =>
      simp only [d22983, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d169395 q = 1) : d170743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22985 q = 1) (hb : d169395 q = 1) : d170744 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22985, d170744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22985, d170744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22986 q = 1) (hb : d169395 q = 1) : d170745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22986, d170745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22986, d170745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22987 q = 1) (hb : d169395 q = 1) : d170746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22987, d170746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22987, d170746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22988 q = 1) (hb : d169395 q = 1) : d170747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22988, d170747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22988, d170747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49395 (p : Pattern) (ha : d23051 p = 1) (hb : d169395 p = 1) : d170755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d169395 q = 1) : d170716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49389 q ha hb
    | true =>
      simp only [d22949, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d169395 q = 1) : d170717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d169395 q = 1) : d170718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22957 q = 1) (hb : d169395 q = 1) : d22957 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22958 q = 1) (hb : d169395 q = 1) : d170719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
    | true =>
      simp only [d22958, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22959 q = 1) (hb : d169395 q = 1) : d170720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22960 q = 1) (hb : d169395 q = 1) : d170721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22961 q = 1) (hb : d169395 q = 1) : d170722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23045 q = 1) (hb : d169395 q = 1) : d23045 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23046 q = 1) (hb : d169395 q = 1) : d170750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23046, d170750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
    | true =>
      simp only [d23046, d170750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23047 q = 1) (hb : d169395 q = 1) : d170751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23047, d170751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23047, d170751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23048 q = 1) (hb : d169395 q = 1) : d170752 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23048, d170752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23048, d170752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23049 q = 1) (hb : d169395 q = 1) : d170753 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23049, d170753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23049, d170753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23050 q = 1) (hb : d169395 q = 1) : d170754 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23050, d170754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23050, d170754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23051 q = 1) (hb : d169395 q = 1) : d170755 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23051, d170755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23051, d170755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro49396 (p : Pattern) (ha : d23057 p = 1) (hb : d169395 p = 1) : d170761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23052 q = 1) (hb : d169395 q = 1) : d170756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23052, d170756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49395 q ha hb
    | true =>
      simp only [d23052, d170756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23053 q = 1) (hb : d169395 q = 1) : d170757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23053, d170757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23053, d170757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23054 q = 1) (hb : d169395 q = 1) : d170758 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23054, d170758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23054, d170758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23055 q = 1) (hb : d169395 q = 1) : d170759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23055, d170759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23055, d170759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23056 q = 1) (hb : d169395 q = 1) : d170760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23056, d170760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23056, d170760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23057 q = 1) (hb : d169395 q = 1) : d170761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23057, d170761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23057, d170761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49397 (p : Pattern) (ha : d150266 p = 1) (hb : d169395 p = 1) : d170767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22989 q = 1) (hb : d169395 q = 1) : d170748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22989, d170748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49393 q ha hb
    | true =>
      simp only [d22989, d170748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49394 q ha hb
  have h2 (q : Pattern) (ha : d150262 q = 1) (hb : d169395 q = 1) : d170749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150262, d170749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150262, d170749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23058 q = 1) (hb : d169395 q = 1) : d170762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23058, d170762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49396 q ha hb
    | true =>
      simp only [d23058, d170762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23059 q = 1) (hb : d169395 q = 1) : d170763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23059, d170763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23059, d170763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150263 q = 1) (hb : d169395 q = 1) : d170764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150263, d170764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150263, d170764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150264 q = 1) (hb : d169395 q = 1) : d170765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150264, d170765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150264, d170765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150265 q = 1) (hb : d169395 q = 1) : d170766 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150265, d170766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150265, d170766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150266 q = 1) (hb : d169395 q = 1) : d170767 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150266, d170767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150266, d170767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49398 (p : Pattern) (ha : d150272 p = 1) (hb : d169395 p = 1) : d170784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22737 q = 1) (hb : d169395 q = 1) : d170575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22737, d170575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22737, d170575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49355 q ha hb
  have h2 (q : Pattern) (ha : d22738 q = 1) (hb : d169395 q = 1) : d170576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22738, d170576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22738, d170576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22747 q = 1) (hb : d169395 q = 1) : d170585 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49355 q ha hb
    | true =>
      simp only [d22747, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49358 q ha hb
  have h4 (q : Pattern) (ha : d22748 q = 1) (hb : d169395 q = 1) : d170586 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22748, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22749 q = 1) (hb : d169395 q = 1) : d170587 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d22749, d170587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22749, d170587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150250 q = 1) (hb : d169395 q = 1) : d170672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150250, d170672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49378 q ha hb
    | true =>
      simp only [d150250, d170672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49386 q ha hb
  have h7 (q : Pattern) (ha : d22916 q = 1) (hb : d169395 q = 1) : d170690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22916, d170690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49361 q ha hb
    | true =>
      simp only [d22916, d170690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49362 q ha hb
  have h8 (q : Pattern) (ha : d150251 q = 1) (hb : d169395 q = 1) : d170691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150251, d170691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150251, d170691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150252 q = 1) (hb : d169395 q = 1) : d170692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150252, d170692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150252, d170692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150253 q = 1) (hb : d169395 q = 1) : d170693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150253, d170693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150253, d170693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150257 q = 1) (hb : d169395 q = 1) : d170697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150257, d170697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150257, d170697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49387 q ha hb
  have h12 (q : Pattern) (ha : d22925 q = 1) (hb : d169395 q = 1) : d170699 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22925, d170699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22925, d170699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49363 q ha hb
  have h13 (q : Pattern) (ha : d150258 q = 1) (hb : d169395 q = 1) : d170700 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150258, d170700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150258, d170700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150259 q = 1) (hb : d169395 q = 1) : d170701 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150259, d170701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150259, d170701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150260 q = 1) (hb : d169395 q = 1) : d170702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150260, d170702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150260, d170702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150261 q = 1) (hb : d169395 q = 1) : d170703 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150261, d170703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150261, d170703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150267 q = 1) (hb : d169395 q = 1) : d170768 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150267, d170768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150267, d170768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49397 q ha hb
  have h18 (q : Pattern) (ha : d23075 q = 1) (hb : d169395 q = 1) : d170779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23075, d170779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23075, d170779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49367 q ha hb
  have h19 (q : Pattern) (ha : d150268 q = 1) (hb : d169395 q = 1) : d170780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150268, d170780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150268, d170780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150269 q = 1) (hb : d169395 q = 1) : d170781 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150269, d170781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150269, d170781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150270 q = 1) (hb : d169395 q = 1) : d170782 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150270, d170782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150270, d170782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150271 q = 1) (hb : d169395 q = 1) : d170783 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150271, d170783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150271, d170783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150272 q = 1) (hb : d169395 q = 1) : d170784 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150272, d170784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150272, d170784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49399 (p : Pattern) (ha : d150278 p = 1) (hb : d169395 p = 1) : d170790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150273 q = 1) (hb : d169395 q = 1) : d170785 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150273, d170785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150273, d170785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49398 q ha hb
  have h2 (q : Pattern) (ha : d150274 q = 1) (hb : d169395 q = 1) : d170786 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150274, d170786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150274, d170786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150275 q = 1) (hb : d169395 q = 1) : d170787 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150275, d170787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150275, d170787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150276 q = 1) (hb : d169395 q = 1) : d170788 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150276, d170788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150276, d170788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150277 q = 1) (hb : d169395 q = 1) : d170789 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150277, d170789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150277, d170789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150278 q = 1) (hb : d169395 q = 1) : d170790 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150278, d170790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150278, d170790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49400 (p : Pattern) (ha : d150284 p = 1) (hb : d169395 p = 1) : d170796 p = 1 := by
  have h0 (q : Pattern) (ha : d150113 q = 1) (hb : d169395 q = 1) : d169789 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150113, d169789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49158 q ha hb
    | true =>
      simp only [d150113, d169789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150153 q = 1) (hb : d169395 q = 1) : d170005 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150153, d170005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150153, d170005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49246 q ha hb
  have h3 (q : Pattern) (ha : d150154 q = 1) (hb : d169395 q = 1) : d170006 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150154, d170006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150154, d170006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150194 q = 1) (hb : d169395 q = 1) : d170270 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150194, d170270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150194, d170270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49297 q ha hb
  have h5 (q : Pattern) (ha : d150195 q = 1) (hb : d169395 q = 1) : d170271 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150195, d170271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150195, d170271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150196 q = 1) (hb : d169395 q = 1) : d170272 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150196, d170272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150196, d170272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150236 q = 1) (hb : d169395 q = 1) : d170534 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150236, d170534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150236, d170534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49348 q ha hb
  have h8 (q : Pattern) (ha : d150237 q = 1) (hb : d169395 q = 1) : d170535 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150237, d170535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150237, d170535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150238 q = 1) (hb : d169395 q = 1) : d170536 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150238, d170536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150238, d170536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150239 q = 1) (hb : d169395 q = 1) : d170537 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150239, d170537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150239, d170537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150279 q = 1) (hb : d169395 q = 1) : d170791 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150279, d170791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150279, d170791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49399 q ha hb
  have h12 (q : Pattern) (ha : d150280 q = 1) (hb : d169395 q = 1) : d170792 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150280, d170792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150280, d170792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150281 q = 1) (hb : d169395 q = 1) : d170793 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150281, d170793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150281, d170793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150282 q = 1) (hb : d169395 q = 1) : d170794 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150282, d170794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150282, d170794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150283 q = 1) (hb : d169395 q = 1) : d170795 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150283, d170795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150283, d170795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150284 q = 1) (hb : d169395 q = 1) : d170796 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150284, d170796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150284, d170796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro49401 (p : Pattern) (ha : d150290 p = 1) (hb : d169395 p = 1) : d170802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150285 q = 1) (hb : d169395 q = 1) : d170797 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150285, d170797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49400 q ha hb
    | true =>
      simp only [d150285, d170797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150286 q = 1) (hb : d169395 q = 1) : d170798 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150286, d170798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150286, d170798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150287 q = 1) (hb : d169395 q = 1) : d170799 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150287, d170799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150287, d170799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150288 q = 1) (hb : d169395 q = 1) : d170800 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150288, d170800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150288, d170800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150289 q = 1) (hb : d169395 q = 1) : d170801 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150289, d170801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150289, d170801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150290 q = 1) (hb : d169395 q = 1) : d170802 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150290, d170802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150290, d170802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49402 (p : Pattern) (ha : d150296 p = 1) (hb : d169395 p = 1) : d170808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150291 q = 1) (hb : d169395 q = 1) : d170803 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150291, d170803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49401 q ha hb
    | true =>
      simp only [d150291, d170803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150292 q = 1) (hb : d169395 q = 1) : d170804 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150292, d170804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150292, d170804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150293 q = 1) (hb : d169395 q = 1) : d170805 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150293, d170805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150293, d170805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150294 q = 1) (hb : d169395 q = 1) : d170806 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150294, d170806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150294, d170806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150295 q = 1) (hb : d169395 q = 1) : d170807 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150295, d170807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150295, d170807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150296 q = 1) (hb : d169395 q = 1) : d170808 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150296, d170808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150296, d170808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49403 (p : Pattern) (ha : d150302 p = 1) (hb : d169397 p = 1) : d170814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150297 q = 1) (hb : d169395 q = 1) : d170809 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150297, d170809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49402 q ha hb
    | true =>
      simp only [d150297, d170809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150298 q = 1) (hb : d169395 q = 1) : d170810 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150298, d170810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150298, d170810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150299 q = 1) (hb : d169395 q = 1) : d170811 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150299, d170811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150299, d170811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150300 q = 1) (hb : d169395 q = 1) : d170812 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150300, d170812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150300, d170812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150301 q = 1) (hb : d169395 q = 1) : d170813 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150301, d170813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150301, d170813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d169396 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150302 q = 1) (hb : d169397 q = 1) : d170814 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150302, d169397, d170814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150302, d169397, d170814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49404 (p : Pattern) (ha : d150308 p = 1) (hb : d169397 p = 1) : d170820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150303 q = 1) (hb : d169397 q = 1) : d170815 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150303, d170815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49403 q ha hb
    | true =>
      simp only [d150303, d170815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150304 q = 1) (hb : d169397 q = 1) : d170816 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150304, d170816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150304, d170816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150305 q = 1) (hb : d169397 q = 1) : d170817 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150305, d170817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150305, d170817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150306 q = 1) (hb : d169397 q = 1) : d170818 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150306, d170818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150306, d170818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150307 q = 1) (hb : d169397 q = 1) : d170819 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150307, d170819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150307, d170819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150308 q = 1) (hb : d169397 q = 1) : d170820 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150308, d170820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150308, d170820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49405 (p : Pattern) (ha : d150314 p = 1) (hb : d169397 p = 1) : d170826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150309 q = 1) (hb : d169397 q = 1) : d170821 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150309, d170821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49404 q ha hb
    | true =>
      simp only [d150309, d170821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150310 q = 1) (hb : d169397 q = 1) : d170822 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150310, d170822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150310, d170822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150311 q = 1) (hb : d169397 q = 1) : d170823 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150311, d170823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150311, d170823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150312 q = 1) (hb : d169397 q = 1) : d170824 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150312, d170824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150312, d170824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150313 q = 1) (hb : d169397 q = 1) : d170825 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150313, d170825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150313, d170825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150314 q = 1) (hb : d169397 q = 1) : d170826 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150314, d170826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150314, d170826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49406 (p : Pattern) (ha : d150320 p = 1) (hb : d169397 p = 1) : d170832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150315 q = 1) (hb : d169397 q = 1) : d170827 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150315, d170827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49405 q ha hb
    | true =>
      simp only [d150315, d170827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150316 q = 1) (hb : d169397 q = 1) : d170828 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150316, d170828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150316, d170828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150317 q = 1) (hb : d169397 q = 1) : d170829 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150317, d170829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150317, d170829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150318 q = 1) (hb : d169397 q = 1) : d170830 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150318, d170830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150318, d170830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150319 q = 1) (hb : d169397 q = 1) : d170831 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150319, d170831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150319, d170831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150320 q = 1) (hb : d169397 q = 1) : d170832 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150320, d170832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150320, d170832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49407 (p : Pattern) (ha : d150326 p = 1) (hb : d169397 p = 1) : d170838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150321 q = 1) (hb : d169397 q = 1) : d170833 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150321, d170833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49406 q ha hb
    | true =>
      simp only [d150321, d170833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150322 q = 1) (hb : d169397 q = 1) : d170834 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150322, d170834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150322, d170834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150323 q = 1) (hb : d169397 q = 1) : d170835 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150323, d170835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150323, d170835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150324 q = 1) (hb : d169397 q = 1) : d170836 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150324, d170836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150324, d170836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150325 q = 1) (hb : d169397 q = 1) : d170837 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150325, d170837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150325, d170837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150326 q = 1) (hb : d169397 q = 1) : d170838 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150326, d170838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150326, d170838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49408 (p : Pattern) (ha : d122308 p = 1) (hb : d169398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d122307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d122307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d122307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d122308 q = 1) (hb : d169398 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122308, d169398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122308, d169398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49409 (p : Pattern) (ha : d122314 p = 1) (hb : d169404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122309 q = 1) (hb : d169399 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122309, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49408 q ha hb
    | true =>
      simp only [d122309, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h2 (q : Pattern) (ha : d122310 q = 1) (hb : d169400 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122310, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122310, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122311 q = 1) (hb : d169401 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122311, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122311, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d122312 q = 1) (hb : d169402 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122312, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122312, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d122313 q = 1) (hb : d169403 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122313, d169403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122313, d169403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122314 q = 1) (hb : d169404 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122314, d169404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122314, d169404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49410 (p : Pattern) (ha : d122320 p = 1) (hb : d169410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49409 q ha hb
    | true =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122318 q = 1) (hb : d169408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122318, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122318, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122319 q = 1) (hb : d169409 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122319, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122319, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122320 q = 1) (hb : d169410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122320, d169410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122320, d169410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49411 (p : Pattern) (ha : d122326 p = 1) (hb : d169416 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d122321 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49410 q ha hb
    | true =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122322 q = 1) (hb : d169412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122322, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122322, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d122323 q = 1) (hb : d169413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122323, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122323, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122324 q = 1) (hb : d169414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122324, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122324, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122325 q = 1) (hb : d169415 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122325, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122325, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122326 q = 1) (hb : d169416 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122326, d169416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122326, d169416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro49412 (p : Pattern) (ha : d122327 p = 1) (hb : d169417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49409 q ha hb
    | true =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122318 q = 1) (hb : d169408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122318, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122318, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122319 q = 1) (hb : d169409 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122319, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122319, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122327 q = 1) (hb : d169417 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122327, d169417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122327, d169417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49413 (p : Pattern) (ha : d122333 p = 1) (hb : d169423 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d122321 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49410 q ha hb
    | true =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122322 q = 1) (hb : d169412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122322, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122322, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d122323 q = 1) (hb : d169413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122323, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122323, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122324 q = 1) (hb : d169414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122324, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122324, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122325 q = 1) (hb : d169415 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122325, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122325, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d122328 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49412 q ha hb
    | true =>
      simp only [d122328, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d122329 q = 1) (hb : d169419 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122329, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d122329, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d122330 q = 1) (hb : d169420 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122330, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d122330, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d122331 q = 1) (hb : d169421 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122331, d169421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d122331, d169421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d122332 q = 1) (hb : d169422 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122332, d169422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d122332, d169422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d122333 q = 1) (hb : d169423 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122333, d169423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122333, d169423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro49414 (p : Pattern) (ha : d122340 p = 1) (hb : d169430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122328 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49412 q ha hb
    | true =>
      simp only [d122328, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122329 q = 1) (hb : d169419 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122329, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122329, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d122330 q = 1) (hb : d169420 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122330, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122330, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122338 q = 1) (hb : d169428 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122338, d169428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122338, d169428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122339 q = 1) (hb : d169429 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122339, d169429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122339, d169429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122340 q = 1) (hb : d169430 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122340, d169430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122340, d169430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49415 (p : Pattern) (ha : d122347 p = 1) (hb : d169436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d122346 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d122346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d122346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h9 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d122347 q = 1) (hb : d169436 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122347, d169436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122347, d169436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49416 (p : Pattern) (ha : d122353 p = 1) (hb : d169442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122348 q = 1) (hb : d169437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122348, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49415 q ha hb
    | true =>
      simp only [d122348, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h2 (q : Pattern) (ha : d122349 q = 1) (hb : d169438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122349, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122349, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122350 q = 1) (hb : d169439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122350, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122350, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d122351 q = 1) (hb : d169440 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122351, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122351, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d122352 q = 1) (hb : d169441 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122352, d169441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122352, d169441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122353 q = 1) (hb : d169442 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122353, d169442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122353, d169442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49417 (p : Pattern) (ha : d122359 p = 1) (hb : d169448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122354 q = 1) (hb : d169443 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122354, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49416 q ha hb
    | true =>
      simp only [d122354, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122355 q = 1) (hb : d169444 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122355, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122355, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122356 q = 1) (hb : d169445 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122356, d169445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122356, d169445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122357 q = 1) (hb : d169446 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122357, d169446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122357, d169446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122358 q = 1) (hb : d169447 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122358, d169447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122358, d169447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122359 q = 1) (hb : d169448 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122359, d169448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122359, d169448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49418 (p : Pattern) (ha : d122365 p = 1) (hb : d169454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122360 q = 1) (hb : d169449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122360, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49417 q ha hb
    | true =>
      simp only [d122360, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122361 q = 1) (hb : d169450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122361, d169450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122361, d169450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d122362 q = 1) (hb : d169451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122362, d169451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122362, d169451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122363 q = 1) (hb : d169452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122363, d169452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122363, d169452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122364 q = 1) (hb : d169453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122364, d169453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122364, d169453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122365 q = 1) (hb : d169454 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122365, d169454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122365, d169454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49419 (p : Pattern) (ha : d122371 p = 1) (hb : d169460 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d122334 q = 1) (hb : d169424 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122334, d169424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49411 q ha hb
    | true =>
      simp only [d122334, d169424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49413 q ha hb
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
  have h8 (q : Pattern) (ha : d122335 q = 1) (hb : d169425 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122335, d169425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122335, d169425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122336 q = 1) (hb : d169426 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122336, d169426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122336, d169426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122337 q = 1) (hb : d169427 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122337, d169427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122337, d169427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122341 q = 1) (hb : d169431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122341, d169431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122341, d169431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49414 q ha hb
  have h12 (q : Pattern) (ha : d122342 q = 1) (hb : d169432 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122342, d169432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122342, d169432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122343 q = 1) (hb : d169433 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122343, d169433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122343, d169433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122344 q = 1) (hb : d169434 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122344, d169434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122344, d169434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122345 q = 1) (hb : d169435 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122345, d169435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122345, d169435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122366 q = 1) (hb : d169455 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122366, d169455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122366, d169455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49418 q ha hb
  have h17 (q : Pattern) (ha : d122367 q = 1) (hb : d169456 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122367, d169456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122367, d169456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d122368 q = 1) (hb : d169457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122368, d169457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122368, d169457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d122369 q = 1) (hb : d169458 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122369, d169458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d122369, d169458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d122370 q = 1) (hb : d169459 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122370, d169459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122370, d169459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122371 q = 1) (hb : d169460 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122371, d169460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122371, d169460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro49420 (p : Pattern) (ha : d122381 p = 1) (hb : d169470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122321 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49410 q ha hb
    | true =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d122377 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122377, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122377, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122378 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122378, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122378, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122379 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122379, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122379, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122380 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122380, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122380, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122381 q = 1) (hb : d169470 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122381, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122381, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49421 (p : Pattern) (ha : d122388 p = 1) (hb : d169477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122321 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49410 q ha hb
    | true =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d122377 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122377, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122377, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122378 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122378, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122378, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122379 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122379, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122379, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122380 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122380, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122380, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122328 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49412 q ha hb
    | true =>
      simp only [d122328, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d122384 q = 1) (hb : d169473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122384, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122384, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122385 q = 1) (hb : d169474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122385, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122385, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122386 q = 1) (hb : d169475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122386, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122386, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122387 q = 1) (hb : d169476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122387, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122387, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122388 q = 1) (hb : d169477 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122388, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122388, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49422 (p : Pattern) (ha : d122393 p = 1) (hb : d169482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49409 q ha hb
    | true =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122318 q = 1) (hb : d169408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122318, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122318, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122392 q = 1) (hb : d169481 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122392, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122392, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122393 q = 1) (hb : d169482 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122393, d169482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122393, d169482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49423 (p : Pattern) (ha : d122400 p = 1) (hb : d169489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49409 q ha hb
    | true =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122398 q = 1) (hb : d169487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122398, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122398, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122399 q = 1) (hb : d169488 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122399, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122399, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122400 q = 1) (hb : d169489 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122400, d169489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122400, d169489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49424 (p : Pattern) (ha : d122406 p = 1) (hb : d169494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122404 q = 1) (hb : d169493 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122404, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122404, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d5451 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
    | true =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5452 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5453 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5454 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5454, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5455 q = 1) (hb : d122405 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d122405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5455, d122405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d122406 q = 1) (hb : d169494 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122406, d169494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122406, d169494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49425 (p : Pattern) (ha : d122412 p = 1) (hb : d169500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122407 q = 1) (hb : d169495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122407, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49424 q ha hb
    | true =>
      simp only [d122407, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49408 q ha hb
  have h2 (q : Pattern) (ha : d122408 q = 1) (hb : d169496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122408, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122408, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122409 q = 1) (hb : d169497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122409, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122409, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122309 q = 1) (hb : d169399 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122309, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49408 q ha hb
    | true =>
      simp only [d122309, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h5 (q : Pattern) (ha : d122310 q = 1) (hb : d169400 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122310, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122310, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122311 q = 1) (hb : d169401 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122311, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122311, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122410 q = 1) (hb : d169498 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122410, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122410, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122312 q = 1) (hb : d169402 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122312, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122312, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d122411 q = 1) (hb : d169499 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122411, d169499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122411, d169499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122412 q = 1) (hb : d169500 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122412, d169500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122412, d169500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49426 (p : Pattern) (ha : d122418 p = 1) (hb : d169506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122413 q = 1) (hb : d169501 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122413, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49425 q ha hb
    | true =>
      simp only [d122413, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122414 q = 1) (hb : d169502 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122414, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122414, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122315 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49409 q ha hb
    | true =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122316 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122415 q = 1) (hb : d169503 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122415, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122415, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122416 q = 1) (hb : d169504 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122416, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122416, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122417 q = 1) (hb : d169505 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122417, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122417, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122418 q = 1) (hb : d169506 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122418, d169506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122418, d169506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49427 (p : Pattern) (ha : d122424 p = 1) (hb : d169512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49409 q ha hb
    | true =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122421 q = 1) (hb : d169509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122421, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122421, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122422 q = 1) (hb : d169510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122422, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122422, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122423 q = 1) (hb : d169511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122423, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122423, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122424 q = 1) (hb : d169512 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122424, d169512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122424, d169512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49428 (p : Pattern) (ha : d122430 p = 1) (hb : d169518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122394 q = 1) (hb : d169483 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122394, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49422 q ha hb
    | true =>
      simp only [d122394, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d122395 q = 1) (hb : d169484 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122395, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122395, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122396 q = 1) (hb : d169485 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122396, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122396, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122397 q = 1) (hb : d169486 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122397, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122397, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122401 q = 1) (hb : d169490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122401, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49423 q ha hb
    | true =>
      simp only [d122401, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d122402 q = 1) (hb : d169491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122402, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122402, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122403 q = 1) (hb : d169492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122403, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122403, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122419 q = 1) (hb : d169507 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122419, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49426 q ha hb
    | true =>
      simp only [d122419, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49410 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122420 q = 1) (hb : d169508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122420, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122425 q = 1) (hb : d169513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122425, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49427 q ha hb
    | true =>
      simp only [d122425, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122426 q = 1) (hb : d169514 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122426, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122426, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122427 q = 1) (hb : d169515 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122427, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122428 q = 1) (hb : d169516 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122428, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122429 q = 1) (hb : d169517 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122429, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122430 q = 1) (hb : d169518 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122430, d169518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122430, d169518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro49429 (p : Pattern) (ha : d122431 p = 1) (hb : d169519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49409 q ha hb
    | true =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122318 q = 1) (hb : d169408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122318, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122318, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122392 q = 1) (hb : d169481 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122392, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122392, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122431 q = 1) (hb : d169519 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122431, d169519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122431, d169519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49430 (p : Pattern) (ha : d122436 p = 1) (hb : d169524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49409 q ha hb
    | true =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122398 q = 1) (hb : d169487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122398, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122398, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122399 q = 1) (hb : d169488 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122399, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122399, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122436 q = 1) (hb : d169524 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122436, d169524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122436, d169524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49431 (p : Pattern) (ha : d122440 p = 1) (hb : d169528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122413 q = 1) (hb : d169501 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122413, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49425 q ha hb
    | true =>
      simp only [d122413, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122414 q = 1) (hb : d169502 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122414, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122414, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122315 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49409 q ha hb
    | true =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122316 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122415 q = 1) (hb : d169503 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122415, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122415, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122416 q = 1) (hb : d169504 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122416, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122416, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122417 q = 1) (hb : d169505 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122417, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122417, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122440 q = 1) (hb : d169528 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122440, d169528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122440, d169528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49432 (p : Pattern) (ha : d122443 p = 1) (hb : d169531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49409 q ha hb
    | true =>
      simp only [d122315, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122421 q = 1) (hb : d169509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122421, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122421, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122422 q = 1) (hb : d169510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122422, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122422, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122423 q = 1) (hb : d169511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122423, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122423, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122443 q = 1) (hb : d169531 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122443, d169531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122443, d169531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49433 (p : Pattern) (ha : d122449 p = 1) (hb : d169537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122394 q = 1) (hb : d169483 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122394, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49422 q ha hb
    | true =>
      simp only [d122394, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d122395 q = 1) (hb : d169484 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122395, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122395, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122396 q = 1) (hb : d169485 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122396, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122396, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122397 q = 1) (hb : d169486 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122397, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122397, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122401 q = 1) (hb : d169490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122401, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49423 q ha hb
    | true =>
      simp only [d122401, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d122402 q = 1) (hb : d169491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122402, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122402, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122403 q = 1) (hb : d169492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122403, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122403, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122419 q = 1) (hb : d169507 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122419, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49426 q ha hb
    | true =>
      simp only [d122419, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49410 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122420 q = 1) (hb : d169508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122420, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122425 q = 1) (hb : d169513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122425, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49427 q ha hb
    | true =>
      simp only [d122425, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122426 q = 1) (hb : d169514 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122426, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122426, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122427 q = 1) (hb : d169515 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122427, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122428 q = 1) (hb : d169516 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122428, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122429 q = 1) (hb : d169517 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122429, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122432 q = 1) (hb : d169520 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122432, d169520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49429 q ha hb
    | true =>
      simp only [d122432, d169520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d122433 q = 1) (hb : d169521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122433, d169521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122433, d169521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122434 q = 1) (hb : d169522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122434, d169522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122434, d169522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d122435 q = 1) (hb : d169523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122435, d169523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122435, d169523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d122437 q = 1) (hb : d169525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122437, d169525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49430 q ha hb
    | true =>
      simp only [d122437, d169525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d122438 q = 1) (hb : d169526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122438, d169526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122438, d169526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d122439 q = 1) (hb : d169527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122439, d169527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122439, d169527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122441 q = 1) (hb : d169529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122441, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49431 q ha hb
    | true =>
      simp only [d122441, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49412 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d122442 q = 1) (hb : d169530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122442, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d122442, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d122444 q = 1) (hb : d169532 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122444, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49432 q ha hb
    | true =>
      simp only [d122444, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d122445 q = 1) (hb : d169533 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122445, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d122445, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d122446 q = 1) (hb : d169534 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122446, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d122446, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122447 q = 1) (hb : d169535 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122447, d169535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d122447, d169535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d122448 q = 1) (hb : d169536 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122448, d169536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122448, d169536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d122449 q = 1) (hb : d169537 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122449, d169537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122449, d169537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro49434 (p : Pattern) (ha : d122451 p = 1) (hb : d169539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122321 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49410 q ha hb
    | true =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d122377 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122377, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122377, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122378 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122378, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122378, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122379 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122379, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122379, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122380 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122380, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122380, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d122451 q = 1) (hb : d169539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122451, d169539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122451, d169539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49435 (p : Pattern) (ha : d122458 p = 1) (hb : d169546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122441 q = 1) (hb : d169529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122441, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49431 q ha hb
    | true =>
      simp only [d122441, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49412 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122442 q = 1) (hb : d169530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122442, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122442, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122444 q = 1) (hb : d169532 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122444, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49432 q ha hb
    | true =>
      simp only [d122444, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122445 q = 1) (hb : d169533 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122445, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122445, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122446 q = 1) (hb : d169534 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122446, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122446, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122456 q = 1) (hb : d169544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122456, d169544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122456, d169544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122457 q = 1) (hb : d169545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122457, d169545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122457, d169545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122458 q = 1) (hb : d169546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122458, d169546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122458, d169546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49436 (p : Pattern) (ha : d122466 p = 1) (hb : d169553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d122464 q = 1) (hb : d169552 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122464, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d122464, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d5495 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
  have h9 (q : Pattern) (ha : d5451 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
    | true =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5496 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5496, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5452 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5497 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5497, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5498 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5498, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5499 q = 1) (hb : d122465 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d122465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5499, d122465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d122466 q = 1) (hb : d169553 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122466, d169553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122466, d169553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49437 (p : Pattern) (ha : d122472 p = 1) (hb : d169559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122467 q = 1) (hb : d169554 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122467, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49436 q ha hb
    | true =>
      simp only [d122467, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49415 q ha hb
  have h2 (q : Pattern) (ha : d122468 q = 1) (hb : d169555 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122468, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122468, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122469 q = 1) (hb : d169556 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122469, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122469, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122348 q = 1) (hb : d169437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122348, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49415 q ha hb
    | true =>
      simp only [d122348, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h5 (q : Pattern) (ha : d122349 q = 1) (hb : d169438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122349, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122349, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122350 q = 1) (hb : d169439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122350, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122350, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122470 q = 1) (hb : d169557 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122470, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122470, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122351 q = 1) (hb : d169440 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122351, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122351, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d122471 q = 1) (hb : d169558 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122471, d169558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122471, d169558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122472 q = 1) (hb : d169559 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122472, d169559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122472, d169559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49438 (p : Pattern) (ha : d122478 p = 1) (hb : d169565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122473 q = 1) (hb : d169560 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122473, d169560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49437 q ha hb
    | true =>
      simp only [d122473, d169560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122474 q = 1) (hb : d169561 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122474, d169561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122474, d169561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122354 q = 1) (hb : d169443 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122354, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49416 q ha hb
    | true =>
      simp only [d122354, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122355 q = 1) (hb : d169444 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122355, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122355, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122475 q = 1) (hb : d169562 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122475, d169562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122475, d169562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122476 q = 1) (hb : d169563 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122476, d169563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122476, d169563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122477 q = 1) (hb : d169564 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122477, d169564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122477, d169564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122478 q = 1) (hb : d169565 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122478, d169565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122478, d169565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49439 (p : Pattern) (ha : d122484 p = 1) (hb : d169571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122354 q = 1) (hb : d169443 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122354, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49416 q ha hb
    | true =>
      simp only [d122354, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122355 q = 1) (hb : d169444 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122355, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122355, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122481 q = 1) (hb : d169568 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122481, d169568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122481, d169568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122482 q = 1) (hb : d169569 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122482, d169569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122482, d169569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122483 q = 1) (hb : d169570 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122483, d169570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122483, d169570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122484 q = 1) (hb : d169571 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122484, d169571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122484, d169571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49440 (p : Pattern) (ha : d122490 p = 1) (hb : d169577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122479 q = 1) (hb : d169566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122479, d169566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49438 q ha hb
    | true =>
      simp only [d122479, d169566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49417 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122480 q = 1) (hb : d169567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122480, d169567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122480, d169567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122485 q = 1) (hb : d169572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122485, d169572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49439 q ha hb
    | true =>
      simp only [d122485, d169572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122486 q = 1) (hb : d169573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122486, d169573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122486, d169573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122487 q = 1) (hb : d169574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122487, d169574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122487, d169574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122488 q = 1) (hb : d169575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122488, d169575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122488, d169575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122489 q = 1) (hb : d169576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122489, d169576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122489, d169576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122490 q = 1) (hb : d169577 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122490, d169577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122490, d169577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49441 (p : Pattern) (ha : d122496 p = 1) (hb : d169583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122382 q = 1) (hb : d169471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122382, d169471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122382, d169471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49420 q ha hb
  have h2 (q : Pattern) (ha : d122383 q = 1) (hb : d169472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122383, d169472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122383, d169472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122389 q = 1) (hb : d169478 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122389, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49420 q ha hb
    | true =>
      simp only [d122389, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49421 q ha hb
  have h4 (q : Pattern) (ha : d122390 q = 1) (hb : d169479 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122390, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122390, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122391 q = 1) (hb : d169480 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122391, d169480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122391, d169480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122450 q = 1) (hb : d169538 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122450, d169538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49428 q ha hb
    | true =>
      simp only [d122450, d169538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49433 q ha hb
  have h7 (q : Pattern) (ha : d122452 q = 1) (hb : d169540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122452, d169540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49434 q ha hb
    | true =>
      simp only [d122452, d169540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d122453 q = 1) (hb : d169541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122453, d169541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122453, d169541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122454 q = 1) (hb : d169542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122454, d169542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122454, d169542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122455 q = 1) (hb : d169543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122455, d169543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122455, d169543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122459 q = 1) (hb : d169547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122459, d169547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122459, d169547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49435 q ha hb
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
  have h13 (q : Pattern) (ha : d122460 q = 1) (hb : d169548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122460, d169548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122460, d169548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122461 q = 1) (hb : d169549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122461, d169549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122461, d169549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122462 q = 1) (hb : d169550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122462, d169550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d122462, d169550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122463 q = 1) (hb : d169551 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122463, d169551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122463, d169551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122491 q = 1) (hb : d169578 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122491, d169578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122491, d169578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49440 q ha hb
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
  have h19 (q : Pattern) (ha : d122492 q = 1) (hb : d169579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122492, d169579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122492, d169579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122493 q = 1) (hb : d169580 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122493, d169580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122493, d169580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122494 q = 1) (hb : d169581 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122494, d169581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d122494, d169581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122495 q = 1) (hb : d169582 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122495, d169582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122495, d169582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122496 q = 1) (hb : d169583 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122496, d169583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122496, d169583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49442 (p : Pattern) (ha : d122502 p = 1) (hb : d169589 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d122372 q = 1) (hb : d169461 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122372, d169461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122372, d169461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49419 q ha hb
  have h6 (q : Pattern) (ha : d122373 q = 1) (hb : d169462 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122373, d169462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122373, d169462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122374 q = 1) (hb : d169463 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122374, d169463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122374, d169463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122375 q = 1) (hb : d169464 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122375, d169464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122375, d169464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122376 q = 1) (hb : d169465 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122376, d169465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122376, d169465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122497 q = 1) (hb : d169584 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122497, d169584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122497, d169584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49441 q ha hb
  have h11 (q : Pattern) (ha : d122498 q = 1) (hb : d169585 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122498, d169585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122498, d169585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122499 q = 1) (hb : d169586 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122499, d169586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122499, d169586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122500 q = 1) (hb : d169587 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122500, d169587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122500, d169587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122501 q = 1) (hb : d169588 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122501, d169588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122501, d169588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122502 q = 1) (hb : d169589 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122502, d169589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122502, d169589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49443 (p : Pattern) (ha : d122505 p = 1) (hb : d169592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122407 q = 1) (hb : d169495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122407, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49424 q ha hb
    | true =>
      simp only [d122407, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49408 q ha hb
  have h2 (q : Pattern) (ha : d122408 q = 1) (hb : d169496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122408, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122408, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122409 q = 1) (hb : d169497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122409, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122409, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122309 q = 1) (hb : d169399 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122309, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49408 q ha hb
    | true =>
      simp only [d122309, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h5 (q : Pattern) (ha : d122310 q = 1) (hb : d169400 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122310, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122310, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122311 q = 1) (hb : d169401 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122311, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122311, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122410 q = 1) (hb : d169498 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122410, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122410, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122503 q = 1) (hb : d169590 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122503, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122503, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122504 q = 1) (hb : d169591 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122504, d169591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122504, d169591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122505 q = 1) (hb : d169592 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122505, d169592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122505, d169592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49444 (p : Pattern) (ha : d122509 p = 1) (hb : d169596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122309 q = 1) (hb : d169399 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122309, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49408 q ha hb
    | true =>
      simp only [d122309, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h2 (q : Pattern) (ha : d122310 q = 1) (hb : d169400 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122310, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122310, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122311 q = 1) (hb : d169401 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122311, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122311, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122503 q = 1) (hb : d169590 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122503, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122503, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122508 q = 1) (hb : d169595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122508, d169595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122508, d169595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122509 q = 1) (hb : d169596 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122509, d169596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122509, d169596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49445 (p : Pattern) (ha : d122515 p = 1) (hb : d169602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49443 q ha hb
    | true =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122513 q = 1) (hb : d169600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122513, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122513, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122514 q = 1) (hb : d169601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122514, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122514, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122515 q = 1) (hb : d169602 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122515, d169602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122515, d169602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49446 (p : Pattern) (ha : d122519 p = 1) (hb : d169606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122517 q = 1) (hb : d169604 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122517, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122517, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122518 q = 1) (hb : d169605 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122518, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122518, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122519 q = 1) (hb : d169606 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122519, d169606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122519, d169606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49447 (p : Pattern) (ha : d122525 p = 1) (hb : d169612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122520 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49445 q ha hb
    | true =>
      simp only [d122520, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49446 q ha hb
  have h2 (q : Pattern) (ha : d122521 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122521, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122521, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122522 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122522, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122522, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122523 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122523, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122523, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122524 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122524, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122524, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122525 q = 1) (hb : d169612 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122525, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122525, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49448 (p : Pattern) (ha : d122528 p = 1) (hb : d169615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49443 q ha hb
    | true =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122513 q = 1) (hb : d169600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122513, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122513, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122514 q = 1) (hb : d169601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122514, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122514, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122528 q = 1) (hb : d169615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122528, d169615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122528, d169615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49449 (p : Pattern) (ha : d122529 p = 1) (hb : d169616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122517 q = 1) (hb : d169604 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122517, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122517, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122518 q = 1) (hb : d169605 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122518, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122518, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122529 q = 1) (hb : d169616 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122529, d169616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122529, d169616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49450 (p : Pattern) (ha : d122535 p = 1) (hb : d169622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122520 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49445 q ha hb
    | true =>
      simp only [d122520, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49446 q ha hb
  have h2 (q : Pattern) (ha : d122521 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122521, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122521, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122522 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122522, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122522, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122523 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122523, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122523, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122524 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122524, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122524, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122530 q = 1) (hb : d169617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122530, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49448 q ha hb
    | true =>
      simp only [d122530, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49449 q ha hb
  have h7 (q : Pattern) (ha : d122531 q = 1) (hb : d169618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122531, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122531, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122532 q = 1) (hb : d169619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122532, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122532, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122533 q = 1) (hb : d169620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122533, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122533, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122534 q = 1) (hb : d169621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122534, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122534, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122535 q = 1) (hb : d169622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122535, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122535, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49451 (p : Pattern) (ha : d122540 p = 1) (hb : d169627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49443 q ha hb
    | true =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122513 q = 1) (hb : d169600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122513, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122513, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122539 q = 1) (hb : d169626 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122539, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122539, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122540 q = 1) (hb : d169627 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122540, d169627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122540, d169627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49452 (p : Pattern) (ha : d122542 p = 1) (hb : d169629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122517 q = 1) (hb : d169604 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122517, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122517, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122541 q = 1) (hb : d169628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122541, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122541, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122542 q = 1) (hb : d169629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122542, d169629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122542, d169629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49453 (p : Pattern) (ha : d122549 p = 1) (hb : d169636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49443 q ha hb
    | true =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122547 q = 1) (hb : d169634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122547, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122547, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122548 q = 1) (hb : d169635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122548, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122548, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122549 q = 1) (hb : d169636 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122549, d169636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122549, d169636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49454 (p : Pattern) (ha : d122552 p = 1) (hb : d169639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122550 q = 1) (hb : d169637 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122550, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122550, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122551 q = 1) (hb : d169638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122551, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122551, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122552 q = 1) (hb : d169639 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122552, d169639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122552, d169639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49455 (p : Pattern) (ha : d122558 p = 1) (hb : d169645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21183 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
    | true =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21184 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21185 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21186 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21186, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122556 q = 1) (hb : d169643 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122556, d169643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122556, d169643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d21189 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46115 q ha hb
    | true =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21190 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21191 q = 1) (hb : d113134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21192 q = 1) (hb : d113135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21192, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d122557 q = 1) (hb : d169644 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122557, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122557, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d122558 q = 1) (hb : d169645 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122558, d169645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122558, d169645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49456 (p : Pattern) (ha : d122562 p = 1) (hb : d169649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5451 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
    | true =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5452 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5453 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5454 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5454, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5455 q = 1) (hb : d122405 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d122405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5455, d122405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d122562 q = 1) (hb : d169649 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122562, d169649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122562, d169649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49457 (p : Pattern) (ha : d122568 p = 1) (hb : d169655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122559 q = 1) (hb : d169646 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122559, d169646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49455 q ha hb
    | true =>
      simp only [d122559, d169646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49424 q ha hb
  have h2 (q : Pattern) (ha : d122560 q = 1) (hb : d169647 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122560, d169647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122560, d169647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122561 q = 1) (hb : d169648 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122561, d169648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122561, d169648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122563 q = 1) (hb : d169650 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122563, d169650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49424 q ha hb
    | true =>
      simp only [d122563, d169650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49456 q ha hb
  have h5 (q : Pattern) (ha : d122564 q = 1) (hb : d169651 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122564, d169651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122564, d169651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122565 q = 1) (hb : d169652 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122565, d169652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122565, d169652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122566 q = 1) (hb : d169653 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122566, d169653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122566, d169653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122407 q = 1) (hb : d169495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122407, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49424 q ha hb
    | true =>
      simp only [d122407, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49408 q ha hb
  have h9 (q : Pattern) (ha : d122408 q = 1) (hb : d169496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122408, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122408, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122409 q = 1) (hb : d169497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122409, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122409, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122309 q = 1) (hb : d169399 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122309, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49408 q ha hb
    | true =>
      simp only [d122309, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h12 (q : Pattern) (ha : d122310 q = 1) (hb : d169400 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122310, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122310, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122311 q = 1) (hb : d169401 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122311, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122311, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122410 q = 1) (hb : d169498 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122410, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122410, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122567 q = 1) (hb : d169654 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122567, d169654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122567, d169654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122568 q = 1) (hb : d169655 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122568, d169655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122568, d169655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro49458 (p : Pattern) (ha : d122574 p = 1) (hb : d169661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122569 q = 1) (hb : d169656 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122569, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49457 q ha hb
    | true =>
      simp only [d122569, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122570 q = 1) (hb : d169657 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122570, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122570, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122506 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49443 q ha hb
    | true =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122507 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122571 q = 1) (hb : d169658 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122571, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122571, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122572 q = 1) (hb : d169659 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122572, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122572, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122573 q = 1) (hb : d169660 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122573, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122573, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122574 q = 1) (hb : d169661 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122574, d169661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122574, d169661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49459 (p : Pattern) (ha : d122580 p = 1) (hb : d169667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49443 q ha hb
    | true =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122577 q = 1) (hb : d169664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122577, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122577, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122578 q = 1) (hb : d169665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122578, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122578, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122579 q = 1) (hb : d169666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122579, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122579, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122580 q = 1) (hb : d169667 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122580, d169667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122580, d169667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49460 (p : Pattern) (ha : d122586 p = 1) (hb : d169673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122543 q = 1) (hb : d169630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122543, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49451 q ha hb
    | true =>
      simp only [d122543, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49452 q ha hb
  have h2 (q : Pattern) (ha : d122544 q = 1) (hb : d169631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122544, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122544, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122545 q = 1) (hb : d169632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122545, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122545, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122546 q = 1) (hb : d169633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122546, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122546, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122553 q = 1) (hb : d169640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122553, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49453 q ha hb
    | true =>
      simp only [d122553, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49454 q ha hb
  have h6 (q : Pattern) (ha : d122554 q = 1) (hb : d169641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122554, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122554, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122555 q = 1) (hb : d169642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122555, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122555, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122575 q = 1) (hb : d169662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122575, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49458 q ha hb
    | true =>
      simp only [d122575, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49445 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122520 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122576 q = 1) (hb : d169663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122576, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122576, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122581 q = 1) (hb : d169668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122581, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49459 q ha hb
    | true =>
      simp only [d122581, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122582 q = 1) (hb : d169669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122582, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122582, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122583 q = 1) (hb : d169670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122583, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122583, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122584 q = 1) (hb : d169671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122584, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122584, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122585 q = 1) (hb : d169672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122585, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122585, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122586 q = 1) (hb : d169673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122586, d169673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122586, d169673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro49461 (p : Pattern) (ha : d122587 p = 1) (hb : d169674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49443 q ha hb
    | true =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122513 q = 1) (hb : d169600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122513, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122513, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122539 q = 1) (hb : d169626 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122539, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122539, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122587 q = 1) (hb : d169674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122587, d169674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122587, d169674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49462 (p : Pattern) (ha : d122588 p = 1) (hb : d169675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122517 q = 1) (hb : d169604 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122517, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122517, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122541 q = 1) (hb : d169628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122541, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122541, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122588 q = 1) (hb : d169675 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122588, d169675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122588, d169675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49463 (p : Pattern) (ha : d122593 p = 1) (hb : d169680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49443 q ha hb
    | true =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122547 q = 1) (hb : d169634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122547, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122547, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122548 q = 1) (hb : d169635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122548, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122548, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122593 q = 1) (hb : d169680 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122593, d169680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122593, d169680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49464 (p : Pattern) (ha : d122594 p = 1) (hb : d169681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49444 q ha hb
    | true =>
      simp only [d122510, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122550 q = 1) (hb : d169637 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122550, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122550, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122551 q = 1) (hb : d169638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122551, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122551, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122594 q = 1) (hb : d169681 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122594, d169681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122594, d169681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49465 (p : Pattern) (ha : d122598 p = 1) (hb : d169685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122569 q = 1) (hb : d169656 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122569, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49457 q ha hb
    | true =>
      simp only [d122569, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122570 q = 1) (hb : d169657 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122570, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122570, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122506 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49443 q ha hb
    | true =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122507 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122571 q = 1) (hb : d169658 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122571, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122571, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122572 q = 1) (hb : d169659 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122572, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122572, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122573 q = 1) (hb : d169660 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122573, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122573, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122598 q = 1) (hb : d169685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122598, d169685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122598, d169685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49466 (p : Pattern) (ha : d122601 p = 1) (hb : d169688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49443 q ha hb
    | true =>
      simp only [d122506, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122577 q = 1) (hb : d169664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122577, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122577, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122578 q = 1) (hb : d169665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122578, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122578, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122579 q = 1) (hb : d169666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122579, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122579, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122601 q = 1) (hb : d169688 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122601, d169688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122601, d169688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49467 (p : Pattern) (ha : d122607 p = 1) (hb : d169694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122543 q = 1) (hb : d169630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122543, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49451 q ha hb
    | true =>
      simp only [d122543, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49452 q ha hb
  have h2 (q : Pattern) (ha : d122544 q = 1) (hb : d169631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122544, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122544, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122545 q = 1) (hb : d169632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122545, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122545, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122546 q = 1) (hb : d169633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122546, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122546, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122553 q = 1) (hb : d169640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122553, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49453 q ha hb
    | true =>
      simp only [d122553, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49454 q ha hb
  have h6 (q : Pattern) (ha : d122554 q = 1) (hb : d169641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122554, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122554, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122555 q = 1) (hb : d169642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122555, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122555, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122575 q = 1) (hb : d169662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122575, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49458 q ha hb
    | true =>
      simp only [d122575, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49445 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122520 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122576 q = 1) (hb : d169663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122576, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122576, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122581 q = 1) (hb : d169668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122581, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49459 q ha hb
    | true =>
      simp only [d122581, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122582 q = 1) (hb : d169669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122582, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122582, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122583 q = 1) (hb : d169670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122583, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122583, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122584 q = 1) (hb : d169671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122584, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122584, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122585 q = 1) (hb : d169672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122585, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122585, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122589 q = 1) (hb : d169676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122589, d169676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49461 q ha hb
    | true =>
      simp only [d122589, d169676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49462 q ha hb
  have h17 (q : Pattern) (ha : d122590 q = 1) (hb : d169677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122590, d169677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122590, d169677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122591 q = 1) (hb : d169678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122591, d169678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122591, d169678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d122592 q = 1) (hb : d169679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122592, d169679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122592, d169679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d122595 q = 1) (hb : d169682 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122595, d169682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49463 q ha hb
    | true =>
      simp only [d122595, d169682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49464 q ha hb
  have h21 (q : Pattern) (ha : d122596 q = 1) (hb : d169683 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122596, d169683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122596, d169683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d122597 q = 1) (hb : d169684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122597, d169684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122597, d169684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122599 q = 1) (hb : d169686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122599, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49465 q ha hb
    | true =>
      simp only [d122599, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49448 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d122530 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d122600 q = 1) (hb : d169687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122600, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d122600, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d122602 q = 1) (hb : d169689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122602, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49466 q ha hb
    | true =>
      simp only [d122602, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d122603 q = 1) (hb : d169690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122603, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d122603, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d122604 q = 1) (hb : d169691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122604, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d122604, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122605 q = 1) (hb : d169692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122605, d169692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d122605, d169692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d122606 q = 1) (hb : d169693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122606, d169693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122606, d169693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d122607 q = 1) (hb : d169694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122607, d169694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122607, d169694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro49468 (p : Pattern) (ha : d122614 p = 1) (hb : d169701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122520 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49445 q ha hb
    | true =>
      simp only [d122520, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49446 q ha hb
  have h2 (q : Pattern) (ha : d122521 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122521, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122521, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122522 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122522, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122522, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122523 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122523, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122523, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122524 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122524, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122524, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122609 q = 1) (hb : d169696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122609, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49446 q ha hb
    | true =>
      simp only [d122609, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122610 q = 1) (hb : d169697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122610, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122610, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122611 q = 1) (hb : d169698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122611, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122611, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122612 q = 1) (hb : d169699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122612, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122612, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122613 q = 1) (hb : d169700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122613, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122613, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122614 q = 1) (hb : d169701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122614, d169701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122614, d169701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49469 (p : Pattern) (ha : d122620 p = 1) (hb : d169707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122609 q = 1) (hb : d169696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122609, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49446 q ha hb
    | true =>
      simp only [d122609, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122610 q = 1) (hb : d169697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122610, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122610, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122611 q = 1) (hb : d169698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122611, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122611, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122612 q = 1) (hb : d169699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122612, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122612, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122613 q = 1) (hb : d169700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122613, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122613, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122615 q = 1) (hb : d169702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122615, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49449 q ha hb
    | true =>
      simp only [d122615, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122616 q = 1) (hb : d169703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122616, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122616, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122617 q = 1) (hb : d169704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122617, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122617, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122618 q = 1) (hb : d169705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122618, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122618, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122619 q = 1) (hb : d169706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122619, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122619, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122620 q = 1) (hb : d169707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122620, d169707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122620, d169707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49470 (p : Pattern) (ha : d122627 p = 1) (hb : d169714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122599 q = 1) (hb : d169686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122599, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49465 q ha hb
    | true =>
      simp only [d122599, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49448 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122530 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122600 q = 1) (hb : d169687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122600, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122600, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122602 q = 1) (hb : d169689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122602, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49466 q ha hb
    | true =>
      simp only [d122602, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122603 q = 1) (hb : d169690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122603, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122603, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122604 q = 1) (hb : d169691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122604, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122604, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122625 q = 1) (hb : d169712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122625, d169712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122625, d169712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122626 q = 1) (hb : d169713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122626, d169713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122626, d169713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122627 q = 1) (hb : d169714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122627, d169714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122627, d169714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49471 (p : Pattern) (ha : d122629 p = 1) (hb : d169716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122615 q = 1) (hb : d169702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122615, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49449 q ha hb
    | true =>
      simp only [d122615, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122616 q = 1) (hb : d169703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122616, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122616, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122617 q = 1) (hb : d169704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122617, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122617, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122618 q = 1) (hb : d169705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122618, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122618, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122619 q = 1) (hb : d169706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122619, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122619, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122629 q = 1) (hb : d169716 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122629, d169716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122629, d169716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49472 (p : Pattern) (ha : d122637 p = 1) (hb : d169724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21309 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
  have h2 (q : Pattern) (ha : d21183 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
    | true =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21310 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21310, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21184 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21311 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21311, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21312 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21312, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d122635 q = 1) (hb : d169722 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122635, d169722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d122635, d169722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d21314 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46115 q ha hb
  have h9 (q : Pattern) (ha : d21189 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46115 q ha hb
    | true =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21315 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21315, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21190 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21316 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21316, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21317 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21317, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d122636 q = 1) (hb : d169723 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122636, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d122636, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122637 q = 1) (hb : d169724 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122637, d169724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122637, d169724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49473 (p : Pattern) (ha : d122641 p = 1) (hb : d169728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5495 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
    | true =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5496 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5496, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5452 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5497 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5497, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5498 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5498, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5499 q = 1) (hb : d122465 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d122465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5499, d122465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h9 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d122641 q = 1) (hb : d169728 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122641, d169728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122641, d169728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49474 (p : Pattern) (ha : d122647 p = 1) (hb : d169734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122638 q = 1) (hb : d169725 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122638, d169725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49472 q ha hb
    | true =>
      simp only [d122638, d169725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49436 q ha hb
  have h2 (q : Pattern) (ha : d122639 q = 1) (hb : d169726 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122639, d169726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122639, d169726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122640 q = 1) (hb : d169727 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122640, d169727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122640, d169727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122642 q = 1) (hb : d169729 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122642, d169729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49436 q ha hb
    | true =>
      simp only [d122642, d169729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49473 q ha hb
  have h5 (q : Pattern) (ha : d122643 q = 1) (hb : d169730 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122643, d169730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122643, d169730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122644 q = 1) (hb : d169731 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122644, d169731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122644, d169731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122645 q = 1) (hb : d169732 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122645, d169732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122645, d169732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122467 q = 1) (hb : d169554 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122467, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49436 q ha hb
    | true =>
      simp only [d122467, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49415 q ha hb
  have h9 (q : Pattern) (ha : d122468 q = 1) (hb : d169555 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122468, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122468, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122469 q = 1) (hb : d169556 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122469, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122469, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122348 q = 1) (hb : d169437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122348, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49415 q ha hb
    | true =>
      simp only [d122348, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h12 (q : Pattern) (ha : d122349 q = 1) (hb : d169438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122349, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122349, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122350 q = 1) (hb : d169439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122350, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122350, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122470 q = 1) (hb : d169557 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122470, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122470, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122646 q = 1) (hb : d169733 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122646, d169733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122646, d169733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122647 q = 1) (hb : d169734 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122647, d169734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122647, d169734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro49475 (p : Pattern) (ha : d122652 p = 1) (hb : d169739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122467 q = 1) (hb : d169554 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122467, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49436 q ha hb
    | true =>
      simp only [d122467, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49415 q ha hb
  have h2 (q : Pattern) (ha : d122468 q = 1) (hb : d169555 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122468, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122468, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122469 q = 1) (hb : d169556 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122469, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122469, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122348 q = 1) (hb : d169437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122348, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49415 q ha hb
    | true =>
      simp only [d122348, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h5 (q : Pattern) (ha : d122349 q = 1) (hb : d169438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122349, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122349, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122350 q = 1) (hb : d169439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122350, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122350, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122470 q = 1) (hb : d169557 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122470, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122470, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122650 q = 1) (hb : d169737 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122650, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122650, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122651 q = 1) (hb : d169738 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122651, d169738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122651, d169738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122652 q = 1) (hb : d169739 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122652, d169739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122652, d169739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49476 (p : Pattern) (ha : d122658 p = 1) (hb : d169745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122648 q = 1) (hb : d169735 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122648, d169735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49474 q ha hb
    | true =>
      simp only [d122648, d169735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122649 q = 1) (hb : d169736 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122649, d169736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122649, d169736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122653 q = 1) (hb : d169740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122653, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49475 q ha hb
    | true =>
      simp only [d122653, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122654 q = 1) (hb : d169741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122654, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122654, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122655 q = 1) (hb : d169742 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122655, d169742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122655, d169742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122656 q = 1) (hb : d169743 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122656, d169743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122656, d169743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122657 q = 1) (hb : d169744 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122657, d169744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122657, d169744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122658 q = 1) (hb : d169745 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122658, d169745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122658, d169745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49477 (p : Pattern) (ha : d122660 p = 1) (hb : d169747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122348 q = 1) (hb : d169437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122348, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49415 q ha hb
    | true =>
      simp only [d122348, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h2 (q : Pattern) (ha : d122349 q = 1) (hb : d169438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122349, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122349, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122350 q = 1) (hb : d169439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122350, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122350, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122650 q = 1) (hb : d169737 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122650, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122650, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122659 q = 1) (hb : d169746 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122659, d169746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122659, d169746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122660 q = 1) (hb : d169747 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122660, d169747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122660, d169747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49478 (p : Pattern) (ha : d122666 p = 1) (hb : d169753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122653 q = 1) (hb : d169740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122653, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49475 q ha hb
    | true =>
      simp only [d122653, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122654 q = 1) (hb : d169741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122654, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122654, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122661 q = 1) (hb : d169748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122661, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49477 q ha hb
    | true =>
      simp only [d122661, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122662 q = 1) (hb : d169749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122662, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122662, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122663 q = 1) (hb : d169750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122663, d169750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122663, d169750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122664 q = 1) (hb : d169751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122664, d169751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122664, d169751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122665 q = 1) (hb : d169752 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122665, d169752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122665, d169752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122666 q = 1) (hb : d169753 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122666, d169753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122666, d169753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49479 (p : Pattern) (ha : d122677 p = 1) (hb : d169759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122653 q = 1) (hb : d169740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122653, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49475 q ha hb
    | true =>
      simp only [d122653, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122654 q = 1) (hb : d169741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122654, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122654, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122674 q = 1) (hb : d169756 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122674, d169756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122674, d169756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122675 q = 1) (hb : d169757 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122675, d169757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122675, d169757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122676 q = 1) (hb : d169758 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122676, d169758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122676, d169758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122677 q = 1) (hb : d169759 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122677, d169759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122677, d169759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49480 (p : Pattern) (ha : d122683 p = 1) (hb : d169765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122667 q = 1) (hb : d169754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122667, d169754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49476 q ha hb
    | true =>
      simp only [d122667, d169754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49478 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122673 q = 1) (hb : d169755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122673, d169755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122673, d169755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122678 q = 1) (hb : d169760 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122678, d169760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49479 q ha hb
    | true =>
      simp only [d122678, d169760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122679 q = 1) (hb : d169761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122679, d169761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122679, d169761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122680 q = 1) (hb : d169762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122680, d169762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122680, d169762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122681 q = 1) (hb : d169763 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122681, d169763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122681, d169763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122682 q = 1) (hb : d169764 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122682, d169764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122682, d169764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122683 q = 1) (hb : d169765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122683, d169765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122683, d169765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49481 (p : Pattern) (ha : d122671 p = 1) (hb : d169770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122661 q = 1) (hb : d169748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122661, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49477 q ha hb
    | true =>
      simp only [d122661, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122662 q = 1) (hb : d169749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122662, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122662, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122668 q = 1) (hb : d169767 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122668, d169767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122668, d169767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122669 q = 1) (hb : d169768 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122669, d169768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122669, d169768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122670 q = 1) (hb : d169769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122670, d169769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122670, d169769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122671 q = 1) (hb : d169770 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122671, d169770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122671, d169770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49482 (p : Pattern) (ha : d122690 p = 1) (hb : d169776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122685 q = 1) (hb : d169771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122685, d169771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49481 q ha hb
    | true =>
      simp only [d122685, d169771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122686 q = 1) (hb : d169772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122686, d169772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122686, d169772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122687 q = 1) (hb : d169773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122687, d169773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122687, d169773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122688 q = 1) (hb : d169774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122688, d169774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122688, d169774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122689 q = 1) (hb : d169775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122689, d169775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122689, d169775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122690 q = 1) (hb : d169776 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122690, d169776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122690, d169776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49483 (p : Pattern) (ha : d122696 p = 1) (hb : d169782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122526 q = 1) (hb : d169613 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122526, d169613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122526, d169613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49447 q ha hb
  have h2 (q : Pattern) (ha : d122527 q = 1) (hb : d169614 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122527, d169614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122527, d169614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122536 q = 1) (hb : d169623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122536, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49447 q ha hb
    | true =>
      simp only [d122536, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49450 q ha hb
  have h4 (q : Pattern) (ha : d122537 q = 1) (hb : d169624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122537, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122537, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122538 q = 1) (hb : d169625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122538, d169625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122538, d169625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122608 q = 1) (hb : d169695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122608, d169695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49460 q ha hb
    | true =>
      simp only [d122608, d169695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49467 q ha hb
  have h7 (q : Pattern) (ha : d122621 q = 1) (hb : d169708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122621, d169708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49468 q ha hb
    | true =>
      simp only [d122621, d169708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49469 q ha hb
  have h8 (q : Pattern) (ha : d122622 q = 1) (hb : d169709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122622, d169709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122622, d169709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122623 q = 1) (hb : d169710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122623, d169710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122623, d169710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122624 q = 1) (hb : d169711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122624, d169711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122624, d169711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122628 q = 1) (hb : d169715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122628, d169715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122628, d169715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49470 q ha hb
  have h12 (q : Pattern) (ha : d122630 q = 1) (hb : d169717 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122630, d169717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122630, d169717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49471 q ha hb
  have h13 (q : Pattern) (ha : d122631 q = 1) (hb : d169718 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122631, d169718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122631, d169718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122632 q = 1) (hb : d169719 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122632, d169719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122632, d169719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122633 q = 1) (hb : d169720 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122633, d169720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d122633, d169720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122634 q = 1) (hb : d169721 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122634, d169721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122634, d169721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122684 q = 1) (hb : d169766 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122684, d169766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122684, d169766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49480 q ha hb
  have h18 (q : Pattern) (ha : d122691 q = 1) (hb : d169777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122691, d169777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122691, d169777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49482 q ha hb
  have h19 (q : Pattern) (ha : d122692 q = 1) (hb : d169778 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122692, d169778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122692, d169778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d122693 q = 1) (hb : d169779 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122693, d169779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122693, d169779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122694 q = 1) (hb : d169780 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122694, d169780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d122694, d169780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122695 q = 1) (hb : d169781 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122695, d169781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122695, d169781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122696 q = 1) (hb : d169782 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122696, d169782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122696, d169782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49484 (p : Pattern) (ha : d122702 p = 1) (hb : d169788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122697 q = 1) (hb : d169783 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122697, d169783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122697, d169783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49483 q ha hb
  have h2 (q : Pattern) (ha : d122698 q = 1) (hb : d169784 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122698, d169784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122698, d169784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122699 q = 1) (hb : d169785 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122699, d169785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122699, d169785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122700 q = 1) (hb : d169786 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122700, d169786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122700, d169786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122701 q = 1) (hb : d169787 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122701, d169787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122701, d169787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122702 q = 1) (hb : d169788 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122702, d169788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122702, d169788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49485 (p : Pattern) (ha : d122704 p = 1) (hb : d169790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122404 q = 1) (hb : d169493 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122404, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122404, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d122704 q = 1) (hb : d169790 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122704, d169790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122704, d169790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49486 (p : Pattern) (ha : d122714 p = 1) (hb : d169800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122705 q = 1) (hb : d169791 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122705, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49455 q ha hb
    | true =>
      simp only [d122705, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49485 q ha hb
  have h2 (q : Pattern) (ha : d122706 q = 1) (hb : d169792 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122706, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122706, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122707 q = 1) (hb : d169793 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122707, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122707, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122708 q = 1) (hb : d169794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122708, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49485 q ha hb
    | true =>
      simp only [d122708, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h5 (q : Pattern) (ha : d122709 q = 1) (hb : d169795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122709, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122709, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122710 q = 1) (hb : d169796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122710, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122710, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122711 q = 1) (hb : d169797 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122711, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122711, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122712 q = 1) (hb : d169798 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122712, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122712, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122713 q = 1) (hb : d169799 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122713, d169799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122713, d169799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122714 q = 1) (hb : d169800 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122714, d169800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122714, d169800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49487 (p : Pattern) (ha : d122718 p = 1) (hb : d169804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122708 q = 1) (hb : d169794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122708, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49485 q ha hb
    | true =>
      simp only [d122708, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h2 (q : Pattern) (ha : d122709 q = 1) (hb : d169795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122709, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122709, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122710 q = 1) (hb : d169796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122710, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122710, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122712 q = 1) (hb : d169798 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122712, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122712, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122717 q = 1) (hb : d169803 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122717, d169803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122717, d169803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122718 q = 1) (hb : d169804 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122718, d169804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122718, d169804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49488 (p : Pattern) (ha : d122724 p = 1) (hb : d169810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49486 q ha hb
    | true =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122722 q = 1) (hb : d169808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122722, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122722, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122723 q = 1) (hb : d169809 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122723, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122723, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122724 q = 1) (hb : d169810 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122724, d169810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122724, d169810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49489 (p : Pattern) (ha : d122728 p = 1) (hb : d169814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122726 q = 1) (hb : d169812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122726, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122726, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122727 q = 1) (hb : d169813 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122727, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122727, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122728 q = 1) (hb : d169814 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122728, d169814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122728, d169814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49490 (p : Pattern) (ha : d122734 p = 1) (hb : d169820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122729 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49488 q ha hb
    | true =>
      simp only [d122729, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49489 q ha hb
  have h2 (q : Pattern) (ha : d122730 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122730, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122730, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122731 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122731, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122731, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122732 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122732, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122732, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122733 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122733, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122733, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122734 q = 1) (hb : d169820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122734, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122734, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49491 (p : Pattern) (ha : d122737 p = 1) (hb : d169823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49486 q ha hb
    | true =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122722 q = 1) (hb : d169808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122722, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122722, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122723 q = 1) (hb : d169809 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122723, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122723, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122737 q = 1) (hb : d169823 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122737, d169823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122737, d169823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49492 (p : Pattern) (ha : d122738 p = 1) (hb : d169824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122726 q = 1) (hb : d169812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122726, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122726, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122727 q = 1) (hb : d169813 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122727, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122727, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122738 q = 1) (hb : d169824 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122738, d169824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122738, d169824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49493 (p : Pattern) (ha : d122744 p = 1) (hb : d169830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122729 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49488 q ha hb
    | true =>
      simp only [d122729, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49489 q ha hb
  have h2 (q : Pattern) (ha : d122730 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122730, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122730, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122731 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122731, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122731, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122732 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122732, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122732, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122733 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122733, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122733, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122739 q = 1) (hb : d169825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122739, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49491 q ha hb
    | true =>
      simp only [d122739, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49492 q ha hb
  have h7 (q : Pattern) (ha : d122740 q = 1) (hb : d169826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122740, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122740, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122741 q = 1) (hb : d169827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122741, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122741, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122742 q = 1) (hb : d169828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122742, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122742, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122743 q = 1) (hb : d169829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122743, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122743, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122744 q = 1) (hb : d169830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122744, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122744, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49494 (p : Pattern) (ha : d122749 p = 1) (hb : d169835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49486 q ha hb
    | true =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122722 q = 1) (hb : d169808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122722, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122722, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122748 q = 1) (hb : d169834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122748, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122748, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122749 q = 1) (hb : d169835 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122749, d169835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122749, d169835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49495 (p : Pattern) (ha : d122751 p = 1) (hb : d169837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122726 q = 1) (hb : d169812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122726, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122726, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122750 q = 1) (hb : d169836 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122750, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122750, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122751 q = 1) (hb : d169837 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122751, d169837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122751, d169837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49496 (p : Pattern) (ha : d122758 p = 1) (hb : d169844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49486 q ha hb
    | true =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122756 q = 1) (hb : d169842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122756, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122756, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122757 q = 1) (hb : d169843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122757, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122757, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122758 q = 1) (hb : d169844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122758, d169844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122758, d169844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49497 (p : Pattern) (ha : d122761 p = 1) (hb : d169847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122759 q = 1) (hb : d169845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122759, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122759, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122760 q = 1) (hb : d169846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122760, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122760, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122761 q = 1) (hb : d169847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122761, d169847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122761, d169847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49498 (p : Pattern) (ha : d122769 p = 1) (hb : d169853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21482 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21482, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46113 q ha hb
    | true =>
      simp only [d21482, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21483 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21483, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21483, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21484 q = 1) (hb : d52513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21484, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21484, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21485 q = 1) (hb : d52514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21485, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21485, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122765 q = 1) (hb : d169851 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122765, d169851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122765, d169851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d21488 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21488, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48817 q ha hb
    | true =>
      simp only [d21488, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21489 q = 1) (hb : d101179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21489, d101179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21489, d101179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21490 q = 1) (hb : d122766 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21490, d122766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21490, d122766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21491 q = 1) (hb : d122767 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21491, d122767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21491, d122767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d122768 q = 1) (hb : d169852 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122768, d169852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122768, d169852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d122769 q = 1) (hb : d169853 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122769, d169853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122769, d169853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49499 (p : Pattern) (ha : d122773 p = 1) (hb : d169857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21189 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46115 q ha hb
    | true =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21190 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21191 q = 1) (hb : d113134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21192 q = 1) (hb : d113135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21192, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122557 q = 1) (hb : d169644 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122557, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122557, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d122773 q = 1) (hb : d169857 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122773, d169857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122773, d169857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
end NetHack.Soko22Hazard87
