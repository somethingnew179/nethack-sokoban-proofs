import NetHack.Soko22Hazard87.AndIntroBlocks0117
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro29500 (p : Pattern) (ha : d13099 p = 1) (hb : d146836 p = 1) : d151970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d146836 q = 1) : d151893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d146836 q = 1) : d151917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13099 q = 1) (hb : d146836 q = 1) : d151970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13099, d151970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13099, d151970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29501 (p : Pattern) (ha : d13104 p = 1) (hb : d146836 p = 1) : d151975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29470 q ha hb
    | true =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d146836 q = 1) : d151923 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d146836 q = 1) : d151924 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13104 q = 1) (hb : d146836 q = 1) : d151975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13104, d151975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13104, d151975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29502 (p : Pattern) (ha : d13105 p = 1) (hb : d146836 p = 1) : d151976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d146836 q = 1) : d151926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d146836 q = 1) : d151927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13105 q = 1) (hb : d146836 q = 1) : d151976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13105, d151976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13105, d151976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29503 (p : Pattern) (ha : d13109 p = 1) (hb : d146836 p = 1) : d151980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d146836 q = 1) : d151942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29495 q ha hb
    | true =>
      simp only [d13037, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d146836 q = 1) : d151943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d146836 q = 1) : d151947 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29478 q ha hb
    | true =>
      simp only [d13041, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d146836 q = 1) : d151948 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d146836 q = 1) : d151949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d146836 q = 1) : d151950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d146836 q = 1) : d151951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13109 q = 1) (hb : d146836 q = 1) : d151980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13109, d151980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13109, d151980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29504 (p : Pattern) (ha : d13110 p = 1) (hb : d146836 p = 1) : d151981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d146836 q = 1) : d151947 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29478 q ha hb
    | true =>
      simp only [d13041, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d146836 q = 1) : d151948 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d146836 q = 1) : d151953 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d146836 q = 1) : d151954 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d146836 q = 1) : d151955 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13110 q = 1) (hb : d146836 q = 1) : d151981 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13110, d151981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13110, d151981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29505 (p : Pattern) (ha : d13116 p = 1) (hb : d146836 p = 1) : d151984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29470 q ha hb
    | true =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d146836 q = 1) : d151959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d146836 q = 1) : d151960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d146836 q = 1) : d151961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13116 q = 1) (hb : d146836 q = 1) : d151984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13116, d151984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13116, d151984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29506 (p : Pattern) (ha : d115405 p = 1) (hb : d146836 p = 1) : d151990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d146836 q = 1) : d151919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29488 q ha hb
    | true =>
      simp only [d13005, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29489 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d146836 q = 1) : d151920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d146836 q = 1) : d151921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d146836 q = 1) : d151922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d146836 q = 1) : d151929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29490 q ha hb
    | true =>
      simp only [d13015, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29491 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d146836 q = 1) : d151930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d146836 q = 1) : d151931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d146836 q = 1) : d151957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29496 q ha hb
    | true =>
      simp only [d13051, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29479 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d146836 q = 1) : d151958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d146836 q = 1) : d151963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29497 q ha hb
    | true =>
      simp only [d13092, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d146836 q = 1) : d151964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d146836 q = 1) : d151965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d146836 q = 1) : d151966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d146836 q = 1) : d151967 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13100 q = 1) (hb : d146836 q = 1) : d151971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13100, d151971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29499 q ha hb
    | true =>
      simp only [d13100, d151971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29500 q ha hb
  have h16 (q : Pattern) (ha : d13101 q = 1) (hb : d146836 q = 1) : d151972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13101, d151972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13101, d151972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13102 q = 1) (hb : d146836 q = 1) : d151973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13102, d151973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13102, d151973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13103 q = 1) (hb : d146836 q = 1) : d151974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13103, d151974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13103, d151974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13106 q = 1) (hb : d146836 q = 1) : d151977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13106, d151977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29501 q ha hb
    | true =>
      simp only [d13106, d151977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29502 q ha hb
  have h20 (q : Pattern) (ha : d13107 q = 1) (hb : d146836 q = 1) : d151978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13107, d151978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13107, d151978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13108 q = 1) (hb : d146836 q = 1) : d151979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13108, d151979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13108, d151979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13111 q = 1) (hb : d146836 q = 1) : d151982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29503 q ha hb
    | true =>
      simp only [d13111, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29504 q ha hb
  have h23 (q : Pattern) (ha : d115401 q = 1) (hb : d146836 q = 1) : d151983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115401, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13117 q = 1) (hb : d146836 q = 1) : d151985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29505 q ha hb
    | true =>
      simp only [d13117, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13118 q = 1) (hb : d146836 q = 1) : d151986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13118, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115402 q = 1) (hb : d146836 q = 1) : d151987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115402, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115403 q = 1) (hb : d146836 q = 1) : d151988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d151988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115403, d151988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115404 q = 1) (hb : d146836 q = 1) : d151989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d151989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115404, d151989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115405 q = 1) (hb : d146836 q = 1) : d151990 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d151990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115405, d151990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29507 (p : Pattern) (ha : d115412 p = 1) (hb : d146836 p = 1) : d152015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13111 q = 1) (hb : d146836 q = 1) : d151982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29503 q ha hb
    | true =>
      simp only [d13111, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29504 q ha hb
  have h2 (q : Pattern) (ha : d115401 q = 1) (hb : d146836 q = 1) : d151983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115401, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13117 q = 1) (hb : d146836 q = 1) : d151985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29505 q ha hb
    | true =>
      simp only [d13117, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13118 q = 1) (hb : d146836 q = 1) : d151986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13118, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115402 q = 1) (hb : d146836 q = 1) : d151987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115402, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115410 q = 1) (hb : d146836 q = 1) : d152013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d152013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115410, d152013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115411 q = 1) (hb : d146836 q = 1) : d152014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d152014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115411, d152014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115412 q = 1) (hb : d146836 q = 1) : d152015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d152015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115412, d152015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29508 (p : Pattern) (ha : d6355 p = 1) (hb : d146836 p = 1) : d152034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6350 q = 1) (hb : d116750 q = 1) : d22073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d22073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6350, d22073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29466 q ha hb
  have h2 (q : Pattern) (ha : d5018 q = 1) (hb : d116750 q = 1) : d21766 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d21766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29466 q ha hb
    | true =>
      simp only [d5018, d21766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6351 q = 1) (hb : d116750 q = 1) : d22074 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d22074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6351, d22074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5019 q = 1) (hb : d116750 q = 1) : d21767 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d21767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5019, d21767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6352 q = 1) (hb : d116750 q = 1) : d22075 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, d22075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6352, d22075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6353 q = 1) (hb : d116750 q = 1) : d22076 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, d22076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6353, d22076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6354 q = 1) (hb : d116750 q = 1) : d22077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d22077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6354, d22077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6355 q = 1) (hb : d146836 q = 1) : d152034 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6355, d146836, d152034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6355, d146836, d152034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29509 (p : Pattern) (ha : d13155 p = 1) (hb : d146836 p = 1) : d149249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d116750 q = 1) : d22024 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d22024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d22024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27936 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d116750 q = 1) : d21835 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27936 q ha hb
    | true =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d116750 q = 1) : d22025 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d22025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d22025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d116750 q = 1) : d21836 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1378 q = 1) (hb : d116750 q = 1) : d22026 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d22026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1378, d22026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1379 q = 1) (hb : d116750 q = 1) : d22027 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d22027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1379, d22027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1380 q = 1) (hb : d116750 q = 1) : d22028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
  have h8 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1381 q = 1) (hb : d116750 q = 1) : d22029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1382 q = 1) (hb : d116750 q = 1) : d22030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1383 q = 1) (hb : d116750 q = 1) : d22031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1384 q = 1) (hb : d116750 q = 1) : d22032 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, d22032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1384, d22032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13155 q = 1) (hb : d146836 q = 1) : d149249 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13155, d146836, d149249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13155, d146836, d149249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29510 (p : Pattern) (ha : d13156 p = 1) (hb : d146836 p = 1) : d149253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d116750 q = 1) : d22028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d116750 q = 1) : d22029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1382 q = 1) (hb : d116750 q = 1) : d22030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1383 q = 1) (hb : d116750 q = 1) : d22031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1385 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
  have h8 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1386 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1387 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1388 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1389 q = 1) (hb : d116750 q = 1) : d22047 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d22047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1389, d22047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13156 q = 1) (hb : d146836 q = 1) : d149253 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13156, d146836, d149253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13156, d146836, d149253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29511 (p : Pattern) (ha : d13169 p = 1) (hb : d146836 p = 1) : d152026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13160 q = 1) (hb : d116750 q = 1) : d22053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d22053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13160, d22053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29493 q ha hb
  have h2 (q : Pattern) (ha : d9814 q = 1) (hb : d116750 q = 1) : d21851 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d21851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29493 q ha hb
    | true =>
      simp only [d9814, d21851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13161 q = 1) (hb : d116750 q = 1) : d22054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d22054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13161, d22054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9816 q = 1) (hb : d116750 q = 1) : d21852 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d21852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9816, d21852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13162 q = 1) (hb : d116750 q = 1) : d22055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13162, d22055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13162, d22055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13163 q = 1) (hb : d116750 q = 1) : d22056 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13163, d22056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13163, d22056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13167 q = 1) (hb : d116750 q = 1) : d13167 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13168 q = 1) (hb : d116750 q = 1) : d22057 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13168, d22057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13168, d22057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13169 q = 1) (hb : d146836 q = 1) : d152026 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13169, d146836, d152026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13169, d146836, d152026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29512 (p : Pattern) (ha : d13179 p = 1) (hb : d146836 p = 1) : d152040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13157 q = 1) (hb : d146836 q = 1) : d152023 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13157, d152023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29509 q ha hb
    | true =>
      simp only [d13157, d152023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29510 q ha hb
  have h2 (q : Pattern) (ha : d13158 q = 1) (hb : d146836 q = 1) : d152024 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13158, d152024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13158, d152024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13159 q = 1) (hb : d146836 q = 1) : d152025 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13159, d152025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13159, d152025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13170 q = 1) (hb : d146836 q = 1) : d152027 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13170, d152027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29510 q ha hb
    | true =>
      simp only [d13170, d152027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29511 q ha hb
  have h5 (q : Pattern) (ha : d13171 q = 1) (hb : d146836 q = 1) : d152028 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13171, d152028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13171, d152028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13172 q = 1) (hb : d146836 q = 1) : d152029 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13172, d152029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13172, d152029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13173 q = 1) (hb : d146836 q = 1) : d152030 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13173, d152030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13173, d152030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13174 q = 1) (hb : d146836 q = 1) : d152031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29510 q ha hb
    | true =>
      simp only [d13174, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29483 q ha hb
  have h9 (q : Pattern) (ha : d13175 q = 1) (hb : d146836 q = 1) : d152032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13176 q = 1) (hb : d146836 q = 1) : d152033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6356 q = 1) (hb : d146836 q = 1) : d152035 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29483 q ha hb
    | true =>
      simp only [d6356, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29508 q ha hb
  have h12 (q : Pattern) (ha : d6357 q = 1) (hb : d146836 q = 1) : d152036 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6358 q = 1) (hb : d146836 q = 1) : d152037 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13177 q = 1) (hb : d146836 q = 1) : d152038 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13177, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13178 q = 1) (hb : d146836 q = 1) : d152039 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13178, d152039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13178, d152039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13179 q = 1) (hb : d146836 q = 1) : d152040 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13179, d152040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13179, d152040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro29513 (p : Pattern) (ha : d13183 p = 1) (hb : d146836 p = 1) : d152045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d146836 q = 1) : d152031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29510 q ha hb
    | true =>
      simp only [d13174, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29483 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d146836 q = 1) : d152032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d146836 q = 1) : d152033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6356 q = 1) (hb : d146836 q = 1) : d152035 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29483 q ha hb
    | true =>
      simp only [d6356, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29508 q ha hb
  have h5 (q : Pattern) (ha : d6357 q = 1) (hb : d146836 q = 1) : d152036 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6358 q = 1) (hb : d146836 q = 1) : d152037 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13177 q = 1) (hb : d146836 q = 1) : d152038 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6359 q = 1) (hb : d146836 q = 1) : d152043 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d152043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6359, d152043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13182 q = 1) (hb : d146836 q = 1) : d152044 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13182, d152044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13182, d152044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13183 q = 1) (hb : d146836 q = 1) : d152045 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13183, d152045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13183, d152045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro29514 (p : Pattern) (ha : d13189 p = 1) (hb : d146836 p = 1) : d152051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13180 q = 1) (hb : d146836 q = 1) : d152041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13180, d152041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29512 q ha hb
    | true =>
      simp only [d13180, d152041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13181 q = 1) (hb : d146836 q = 1) : d152042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13181, d152042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13181, d152042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13184 q = 1) (hb : d146836 q = 1) : d152046 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29513 q ha hb
    | true =>
      simp only [d13184, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13185 q = 1) (hb : d146836 q = 1) : d152047 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13186 q = 1) (hb : d146836 q = 1) : d152048 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13186, d152048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13186, d152048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13187 q = 1) (hb : d146836 q = 1) : d152049 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13187, d152049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13187, d152049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13188 q = 1) (hb : d146836 q = 1) : d152050 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13188, d152050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13188, d152050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13189 q = 1) (hb : d146836 q = 1) : d152051 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13189, d152051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13189, d152051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29515 (p : Pattern) (ha : d13202 p = 1) (hb : d146836 p = 1) : d152063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13184 q = 1) (hb : d146836 q = 1) : d152046 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29513 q ha hb
    | true =>
      simp only [d13184, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13185 q = 1) (hb : d146836 q = 1) : d152047 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d146836 q = 1) : d152058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29485 q ha hb
    | true =>
      simp only [d13197, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d146836 q = 1) : d152059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13199 q = 1) (hb : d146836 q = 1) : d152060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13199, d152060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13199, d152060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13200 q = 1) (hb : d146836 q = 1) : d152061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13200, d152061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13200, d152061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13201 q = 1) (hb : d146836 q = 1) : d152062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13201, d152062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13201, d152062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13202 q = 1) (hb : d146836 q = 1) : d152063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13202, d152063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13202, d152063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29516 (p : Pattern) (ha : d13243 p = 1) (hb : d146836 p = 1) : d152067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d146836 q = 1) : d152031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29510 q ha hb
    | true =>
      simp only [d13174, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29483 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d146836 q = 1) : d152032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d146836 q = 1) : d152033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6356 q = 1) (hb : d146836 q = 1) : d152035 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29483 q ha hb
    | true =>
      simp only [d6356, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29508 q ha hb
  have h5 (q : Pattern) (ha : d6357 q = 1) (hb : d146836 q = 1) : d152036 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6358 q = 1) (hb : d146836 q = 1) : d152037 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13177 q = 1) (hb : d146836 q = 1) : d152038 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13191 q = 1) (hb : d146836 q = 1) : d152052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29483 q ha hb
    | true =>
      simp only [d13191, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29484 q ha hb
  have h9 (q : Pattern) (ha : d13192 q = 1) (hb : d146836 q = 1) : d152053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13193 q = 1) (hb : d146836 q = 1) : d152054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13194 q = 1) (hb : d146836 q = 1) : d152055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13194, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13242 q = 1) (hb : d146836 q = 1) : d152066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13242, d152066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13242, d152066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13243 q = 1) (hb : d146836 q = 1) : d152067 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13243, d152067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13243, d152067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro29517 (p : Pattern) (ha : d13249 p = 1) (hb : d146836 p = 1) : d152073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d146836 q = 1) : d152068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29516 q ha hb
    | true =>
      simp only [d13244, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d146836 q = 1) : d152069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13246 q = 1) (hb : d146836 q = 1) : d152070 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13246, d152070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13246, d152070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13247 q = 1) (hb : d146836 q = 1) : d152071 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13247, d152071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13247, d152071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13248 q = 1) (hb : d146836 q = 1) : d152072 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13248, d152072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13248, d152072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13249 q = 1) (hb : d146836 q = 1) : d152073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13249, d152073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13249, d152073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29518 (p : Pattern) (ha : d115422 p = 1) (hb : d146836 p = 1) : d152079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13203 q = 1) (hb : d146836 q = 1) : d152064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13203, d152064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29514 q ha hb
    | true =>
      simp only [d13203, d152064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29515 q ha hb
  have h2 (q : Pattern) (ha : d115418 q = 1) (hb : d146836 q = 1) : d152065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d152065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115418, d152065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13250 q = 1) (hb : d146836 q = 1) : d152074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13250, d152074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29517 q ha hb
    | true =>
      simp only [d13250, d152074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13251 q = 1) (hb : d146836 q = 1) : d152075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13251, d152075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13251, d152075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115419 q = 1) (hb : d146836 q = 1) : d152076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d152076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115419, d152076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115420 q = 1) (hb : d146836 q = 1) : d152077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d152077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115420, d152077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115421 q = 1) (hb : d146836 q = 1) : d152078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d152078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115421, d152078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115422 q = 1) (hb : d146836 q = 1) : d152079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d152079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115422, d152079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29519 (p : Pattern) (ha : d115428 p = 1) (hb : d146836 p = 1) : d152096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12988 q = 1) (hb : d146836 q = 1) : d151902 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12988, d151902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12988, d151902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29474 q ha hb
  have h2 (q : Pattern) (ha : d12989 q = 1) (hb : d146836 q = 1) : d151903 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12989, d151903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12989, d151903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12998 q = 1) (hb : d146836 q = 1) : d151912 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29474 q ha hb
    | true =>
      simp only [d12998, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29477 q ha hb
  have h4 (q : Pattern) (ha : d12999 q = 1) (hb : d146836 q = 1) : d151913 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12999, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13000 q = 1) (hb : d146836 q = 1) : d151914 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13000, d151914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13000, d151914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115406 q = 1) (hb : d146836 q = 1) : d151991 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d151991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29498 q ha hb
    | true =>
      simp only [d115406, d151991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29506 q ha hb
  have h7 (q : Pattern) (ha : d13141 q = 1) (hb : d146836 q = 1) : d152009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13141, d152009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29480 q ha hb
    | true =>
      simp only [d13141, d152009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29481 q ha hb
  have h8 (q : Pattern) (ha : d115407 q = 1) (hb : d146836 q = 1) : d152010 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d152010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115407, d152010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115408 q = 1) (hb : d146836 q = 1) : d152011 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d152011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115408, d152011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115409 q = 1) (hb : d146836 q = 1) : d152012 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d152012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115409, d152012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115413 q = 1) (hb : d146836 q = 1) : d152016 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d152016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115413, d152016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29507 q ha hb
  have h12 (q : Pattern) (ha : d13150 q = 1) (hb : d146836 q = 1) : d152018 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13150, d152018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13150, d152018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29482 q ha hb
  have h13 (q : Pattern) (ha : d115414 q = 1) (hb : d146836 q = 1) : d152019 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d152019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115414, d152019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115415 q = 1) (hb : d146836 q = 1) : d152020 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d152020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115415, d152020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115416 q = 1) (hb : d146836 q = 1) : d152021 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d152021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115416, d152021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115417 q = 1) (hb : d146836 q = 1) : d152022 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d152022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115417, d152022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115423 q = 1) (hb : d146836 q = 1) : d152080 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d152080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115423, d152080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29518 q ha hb
  have h18 (q : Pattern) (ha : d13267 q = 1) (hb : d146836 q = 1) : d152091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13267, d152091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13267, d152091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29487 q ha hb
  have h19 (q : Pattern) (ha : d115424 q = 1) (hb : d146836 q = 1) : d152092 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d152092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115424, d152092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115425 q = 1) (hb : d146836 q = 1) : d152093 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d152093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115425, d152093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115426 q = 1) (hb : d146836 q = 1) : d152094 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d152094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115426, d152094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115427 q = 1) (hb : d146836 q = 1) : d152095 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d152095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115427, d152095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115428 q = 1) (hb : d146836 q = 1) : d152096 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d152096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115428, d152096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29520 (p : Pattern) (ha : d115434 p = 1) (hb : d146836 p = 1) : d152102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115429 q = 1) (hb : d146836 q = 1) : d152097 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d152097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115429, d152097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29519 q ha hb
  have h2 (q : Pattern) (ha : d115430 q = 1) (hb : d146836 q = 1) : d152098 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d152098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115430, d152098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115431 q = 1) (hb : d146836 q = 1) : d152099 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d152099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115431, d152099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115432 q = 1) (hb : d146836 q = 1) : d152100 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d152100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115432, d152100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115433 q = 1) (hb : d146836 q = 1) : d152101 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d152101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115433, d152101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115434 q = 1) (hb : d146836 q = 1) : d152102 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d152102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115434, d152102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29521 (p : Pattern) (ha : d5120 p = 1) (hb : d146836 p = 1) : d149326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1584 q = 1) (hb : d116750 q = 1) : d22235 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1585 q = 1) (hb : d116750 q = 1) : d22236 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1586 q = 1) (hb : d116750 q = 1) : d22237 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d22237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1586, d22237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5120 q = 1) (hb : d146836 q = 1) : d149326 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5120, d146836, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5120, d146836, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29522 (p : Pattern) (ha : d5133 p = 1) (hb : d116750 p = 1) : d22243 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5127 q = 1) : d5127 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5133 q = 1) (hb : d116750 q = 1) : d22243 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5133, d116750, d22243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5133, d116750, d22243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro29523 (p : Pattern) (ha : d5139 p = 1) (hb : d146836 p = 1) : d152109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5134 q = 1) (hb : d116750 q = 1) : d22244 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d22244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29522 q ha hb
    | true =>
      simp only [d5134, d22244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5135 q = 1) (hb : d116750 q = 1) : d22245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d22245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5135, d22245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5136 q = 1) (hb : d116750 q = 1) : d22246 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, d22246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5136, d22246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5137 q = 1) (hb : d116750 q = 1) : d22247 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, d22247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5137, d22247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5138 q = 1) (hb : d116750 q = 1) : d22248 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d22248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5138, d22248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5139 q = 1) (hb : d146836 q = 1) : d152109 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5139, d146836, d152109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5139, d146836, d152109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29524 (p : Pattern) (ha : d13282 p = 1) (hb : d146836 p = 1) : d149322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d116750 q = 1) : d10036 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
    | true =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d116750 q = 1) : d10038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d116750 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d116750 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1572 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1573 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1574 q = 1) (hb : d116750 q = 1) : d22224 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d22224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1574, d22224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13282 q = 1) (hb : d146836 q = 1) : d149322 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13282, d146836, d149322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13282, d146836, d149322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29525 (p : Pattern) (ha : d13287 p = 1) (hb : d146836 p = 1) : d22421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d116750 q = 1) : d22235 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d116750 q = 1) : d22236 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d116750 q = 1) : d22254 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d22254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d22254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13287 q = 1) (hb : d146836 q = 1) : d22421 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, d146836, d22421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13287, d146836, d22421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29526 (p : Pattern) (ha : d13293 p = 1) (hb : d146836 p = 1) : d152119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d146836 q = 1) : d152106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29524 q ha hb
    | true =>
      simp only [d13283, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29521 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d146836 q = 1) : d152107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d146836 q = 1) : d152108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5140 q = 1) (hb : d146836 q = 1) : d152110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29521 q ha hb
    | true =>
      simp only [d5140, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29523 q ha hb
  have h5 (q : Pattern) (ha : d5141 q = 1) (hb : d146836 q = 1) : d152111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5142 q = 1) (hb : d146836 q = 1) : d152112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13286 q = 1) (hb : d146836 q = 1) : d152113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13288 q = 1) (hb : d146836 q = 1) : d152114 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29521 q ha hb
    | true =>
      simp only [d13288, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29525 q ha hb
  have h9 (q : Pattern) (ha : d13289 q = 1) (hb : d146836 q = 1) : d152115 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13290 q = 1) (hb : d146836 q = 1) : d152116 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13291 q = 1) (hb : d146836 q = 1) : d152117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13291, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13292 q = 1) (hb : d146836 q = 1) : d152118 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13292, d152118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13292, d152118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13293 q = 1) (hb : d146836 q = 1) : d152119 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13293, d152119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13293, d152119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro29527 (p : Pattern) (ha : d13297 p = 1) (hb : d146836 p = 1) : d152123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13288 q = 1) (hb : d146836 q = 1) : d152114 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29521 q ha hb
    | true =>
      simp only [d13288, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29525 q ha hb
  have h2 (q : Pattern) (ha : d13289 q = 1) (hb : d146836 q = 1) : d152115 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13290 q = 1) (hb : d146836 q = 1) : d152116 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13291 q = 1) (hb : d146836 q = 1) : d152117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13291, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13296 q = 1) (hb : d146836 q = 1) : d152122 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13296, d152122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13296, d152122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13297 q = 1) (hb : d146836 q = 1) : d152123 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13297, d152123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13297, d152123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29528 (p : Pattern) (ha : d13303 p = 1) (hb : d146836 p = 1) : d152129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29526 q ha hb
    | true =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d146836 q = 1) : d152127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d146836 q = 1) : d152128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13303 q = 1) (hb : d146836 q = 1) : d152129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13303, d152129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13303, d152129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29529 (p : Pattern) (ha : d13307 p = 1) (hb : d146836 p = 1) : d152133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d146836 q = 1) : d152131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d146836 q = 1) : d152132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13307 q = 1) (hb : d146836 q = 1) : d152133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13307, d152133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13307, d152133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29530 (p : Pattern) (ha : d13313 p = 1) (hb : d146836 p = 1) : d152139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d146836 q = 1) : d152134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29528 q ha hb
    | true =>
      simp only [d13308, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29529 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d146836 q = 1) : d152135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d146836 q = 1) : d152136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d146836 q = 1) : d152137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d146836 q = 1) : d152138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13313 q = 1) (hb : d146836 q = 1) : d152139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13313, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13313, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29531 (p : Pattern) (ha : d13316 p = 1) (hb : d146836 p = 1) : d152142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29526 q ha hb
    | true =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d146836 q = 1) : d152127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d146836 q = 1) : d152128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13316 q = 1) (hb : d146836 q = 1) : d152142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13316, d152142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13316, d152142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29532 (p : Pattern) (ha : d13317 p = 1) (hb : d146836 p = 1) : d152143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d146836 q = 1) : d152131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d146836 q = 1) : d152132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13317 q = 1) (hb : d146836 q = 1) : d152143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13317, d152143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13317, d152143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29533 (p : Pattern) (ha : d13323 p = 1) (hb : d146836 p = 1) : d152149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d146836 q = 1) : d152134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29528 q ha hb
    | true =>
      simp only [d13308, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29529 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d146836 q = 1) : d152135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d146836 q = 1) : d152136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d146836 q = 1) : d152137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d146836 q = 1) : d152138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13318 q = 1) (hb : d146836 q = 1) : d152144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29531 q ha hb
    | true =>
      simp only [d13318, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29532 q ha hb
  have h7 (q : Pattern) (ha : d13319 q = 1) (hb : d146836 q = 1) : d152145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13320 q = 1) (hb : d146836 q = 1) : d152146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13320, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13321 q = 1) (hb : d146836 q = 1) : d152147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13322 q = 1) (hb : d146836 q = 1) : d152148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13323 q = 1) (hb : d146836 q = 1) : d152149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13323, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13323, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29534 (p : Pattern) (ha : d13366 p = 1) (hb : d146836 p = 1) : d152184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d146836 q = 1) : d152106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29524 q ha hb
    | true =>
      simp only [d13283, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29521 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d146836 q = 1) : d152107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d146836 q = 1) : d152108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5140 q = 1) (hb : d146836 q = 1) : d152110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29521 q ha hb
    | true =>
      simp only [d5140, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29523 q ha hb
  have h5 (q : Pattern) (ha : d5141 q = 1) (hb : d146836 q = 1) : d152111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5142 q = 1) (hb : d146836 q = 1) : d152112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13286 q = 1) (hb : d146836 q = 1) : d152113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5143 q = 1) (hb : d146836 q = 1) : d152182 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d152182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5143, d152182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13365 q = 1) (hb : d146836 q = 1) : d152183 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13365, d152183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13365, d152183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13366 q = 1) (hb : d146836 q = 1) : d152184 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13366, d152184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13366, d152184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro29535 (p : Pattern) (ha : d13376 p = 1) (hb : d146836 p = 1) : d152194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d146836 q = 1) : d152185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29534 q ha hb
    | true =>
      simp only [d13367, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d146836 q = 1) : d152186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d146836 q = 1) : d152191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d146836 q = 1) : d152192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d146836 q = 1) : d152193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13376 q = 1) (hb : d146836 q = 1) : d152194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13376, d152194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13376, d152194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29536 (p : Pattern) (ha : d13460 p = 1) (hb : d146836 p = 1) : d152240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13450 q = 1) (hb : d146836 q = 1) : d152230 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13450, d152230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29535 q ha hb
    | true =>
      simp only [d13450, d152230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29529 q ha hb
  have h2 (q : Pattern) (ha : d13451 q = 1) (hb : d146836 q = 1) : d152231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13451, d152231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13451, d152231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13452 q = 1) (hb : d146836 q = 1) : d152232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13452, d152232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13452, d152232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13453 q = 1) (hb : d146836 q = 1) : d152233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13453, d152233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13453, d152233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13454 q = 1) (hb : d146836 q = 1) : d152234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13454, d152234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13454, d152234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13455 q = 1) (hb : d146836 q = 1) : d152235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29529 q ha hb
    | true =>
      simp only [d13455, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13456 q = 1) (hb : d146836 q = 1) : d152236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13457 q = 1) (hb : d146836 q = 1) : d152237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13457, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13458 q = 1) (hb : d146836 q = 1) : d152238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13459 q = 1) (hb : d146836 q = 1) : d152239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13460 q = 1) (hb : d146836 q = 1) : d152240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13460, d152240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13460, d152240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29537 (p : Pattern) (ha : d13466 p = 1) (hb : d146836 p = 1) : d152246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13455 q = 1) (hb : d146836 q = 1) : d152235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29529 q ha hb
    | true =>
      simp only [d13455, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13456 q = 1) (hb : d146836 q = 1) : d152236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13457 q = 1) (hb : d146836 q = 1) : d152237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13457, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13458 q = 1) (hb : d146836 q = 1) : d152238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13459 q = 1) (hb : d146836 q = 1) : d152239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13461 q = 1) (hb : d146836 q = 1) : d152241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29532 q ha hb
    | true =>
      simp only [d13461, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13462 q = 1) (hb : d146836 q = 1) : d152242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13463 q = 1) (hb : d146836 q = 1) : d152243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13463, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13464 q = 1) (hb : d146836 q = 1) : d152244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13465 q = 1) (hb : d146836 q = 1) : d152245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13466 q = 1) (hb : d146836 q = 1) : d152246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13466, d152246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13466, d152246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29538 (p : Pattern) (ha : d13475 p = 1) (hb : d146836 p = 1) : d152255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13461 q = 1) (hb : d146836 q = 1) : d152241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29532 q ha hb
    | true =>
      simp only [d13461, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13462 q = 1) (hb : d146836 q = 1) : d152242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13463 q = 1) (hb : d146836 q = 1) : d152243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13463, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13464 q = 1) (hb : d146836 q = 1) : d152244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13465 q = 1) (hb : d146836 q = 1) : d152245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13475 q = 1) (hb : d146836 q = 1) : d152255 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13475, d152255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13475, d152255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29539 (p : Pattern) (ha : d6495 p = 1) (hb : d146836 p = 1) : d149466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d116750 q = 1) : d22508 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d116750 q = 1) : d22509 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d116750 q = 1) : d22510 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d116750 q = 1) : d22511 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1868 q = 1) (hb : d116750 q = 1) : d22529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
  have h8 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1869 q = 1) (hb : d116750 q = 1) : d22530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1870 q = 1) (hb : d116750 q = 1) : d22531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1871 q = 1) (hb : d116750 q = 1) : d22532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1872 q = 1) (hb : d116750 q = 1) : d22533 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d22533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1872, d22533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6495 q = 1) (hb : d146836 q = 1) : d149466 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6495, d146836, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6495, d146836, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29540 (p : Pattern) (ha : d13516 p = 1) (hb : d146836 p = 1) : d22639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d116750 q = 1) : d22529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1869 q = 1) (hb : d116750 q = 1) : d22530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1870 q = 1) (hb : d116750 q = 1) : d22531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1871 q = 1) (hb : d116750 q = 1) : d22532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1877 q = 1) (hb : d116750 q = 1) : d22561 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d22561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d22561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13516 q = 1) (hb : d146836 q = 1) : d22639 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, d146836, d22639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13516, d146836, d22639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29541 (p : Pattern) (ha : d13522 p = 1) (hb : d146836 p = 1) : d152295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13517 q = 1) (hb : d146836 q = 1) : d152290 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29539 q ha hb
    | true =>
      simp only [d13517, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29540 q ha hb
  have h2 (q : Pattern) (ha : d13518 q = 1) (hb : d146836 q = 1) : d152291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13519 q = 1) (hb : d146836 q = 1) : d152292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13520 q = 1) (hb : d146836 q = 1) : d152293 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13520, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13521 q = 1) (hb : d146836 q = 1) : d152294 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13521, d152294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13521, d152294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13522 q = 1) (hb : d146836 q = 1) : d152295 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13522, d152295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13522, d152295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29542 (p : Pattern) (ha : d13586 p = 1) (hb : d146836 p = 1) : d152322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13523 q = 1) (hb : d146836 q = 1) : d152296 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29541 q ha hb
    | true =>
      simp only [d13523, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13524 q = 1) (hb : d146836 q = 1) : d152297 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13583 q = 1) (hb : d146836 q = 1) : d152319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13583, d152319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13583, d152319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13584 q = 1) (hb : d146836 q = 1) : d152320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13584, d152320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13584, d152320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13585 q = 1) (hb : d146836 q = 1) : d152321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13585, d152321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13585, d152321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13586 q = 1) (hb : d146836 q = 1) : d152322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13586, d152322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13586, d152322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29543 (p : Pattern) (ha : d13592 p = 1) (hb : d146836 p = 1) : d152328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13587 q = 1) (hb : d146836 q = 1) : d152323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13587, d152323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29542 q ha hb
    | true =>
      simp only [d13587, d152323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13588 q = 1) (hb : d146836 q = 1) : d152324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13588, d152324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13588, d152324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13589 q = 1) (hb : d146836 q = 1) : d152325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13589, d152325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13589, d152325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13590 q = 1) (hb : d146836 q = 1) : d152326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13590, d152326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13590, d152326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13591 q = 1) (hb : d146836 q = 1) : d152327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13591, d152327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13591, d152327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13592 q = 1) (hb : d146836 q = 1) : d152328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13592, d152328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13592, d152328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29544 (p : Pattern) (ha : d13328 p = 1) (hb : d146836 p = 1) : d152154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29526 q ha hb
    | true =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d146836 q = 1) : d152127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d146836 q = 1) : d152153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13328 q = 1) (hb : d146836 q = 1) : d152154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13328, d152154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13328, d152154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29545 (p : Pattern) (ha : d13330 p = 1) (hb : d146836 p = 1) : d152156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d146836 q = 1) : d152131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d146836 q = 1) : d152155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13330 q = 1) (hb : d146836 q = 1) : d152156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13330, d152156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13330, d152156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29546 (p : Pattern) (ha : d13337 p = 1) (hb : d146836 p = 1) : d152163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29526 q ha hb
    | true =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d146836 q = 1) : d152161 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d146836 q = 1) : d152162 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13337 q = 1) (hb : d146836 q = 1) : d152163 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13337, d152163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13337, d152163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29547 (p : Pattern) (ha : d13340 p = 1) (hb : d146836 p = 1) : d152166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d146836 q = 1) : d152164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d146836 q = 1) : d152165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d146836 q = 1) : d152166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13340, d152166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13340, d152166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29548 (p : Pattern) (ha : d13344 p = 1) (hb : d146836 p = 1) : d149384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d116750 q = 1) : d22313 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d22313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27985 q ha hb
    | true =>
      simp only [d1665, d22313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d116750 q = 1) : d22314 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d22314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, d22314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d116750 q = 1) : d22315 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d22315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d22315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d116750 q = 1) : d22316 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d22316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, d22316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1555 q = 1) (hb : d116750 q = 1) : d10036 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
    | true =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1556 q = 1) (hb : d116750 q = 1) : d10038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1557 q = 1) (hb : d116750 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1558 q = 1) (hb : d116750 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1669 q = 1) (hb : d116750 q = 1) : d22317 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1669, d22317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1669, d22317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13344 q = 1) (hb : d146836 q = 1) : d149384 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13344, d146836, d149384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13344, d146836, d149384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29549 (p : Pattern) (ha : d10098 p = 1) (hb : d116750 p = 1) : d22323 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d10097 q = 1) : d10097 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10061 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10098 q = 1) (hb : d116750 q = 1) : d22323 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10098, d116750, d22323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10098, d116750, d22323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro29550 (p : Pattern) (ha : d13356 p = 1) (hb : d146836 p = 1) : d152173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10099 q = 1) (hb : d116750 q = 1) : d22324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d22324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29549 q ha hb
    | true =>
      simp only [d10099, d22324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10101 q = 1) (hb : d116750 q = 1) : d22325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d22325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10101, d22325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13348 q = 1) (hb : d116750 q = 1) : d22326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, d22326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13348, d22326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13349 q = 1) (hb : d116750 q = 1) : d22327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, d22327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13349, d22327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13354 q = 1) (hb : d116750 q = 1) : d13354 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13355 q = 1) (hb : d116750 q = 1) : d22328 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13355, d22328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13355, d22328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13356 q = 1) (hb : d146836 q = 1) : d152173 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13356, d146836, d152173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13356, d146836, d152173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29551 (p : Pattern) (ha : d13362 p = 1) (hb : d146836 p = 1) : d152179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13345 q = 1) (hb : d146836 q = 1) : d152170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13345, d152170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29548 q ha hb
    | true =>
      simp only [d13345, d152170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29524 q ha hb
  have h2 (q : Pattern) (ha : d13346 q = 1) (hb : d146836 q = 1) : d152171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13346, d152171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13346, d152171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13347 q = 1) (hb : d146836 q = 1) : d152172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13347, d152172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13347, d152172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13357 q = 1) (hb : d146836 q = 1) : d152174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13357, d152174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29524 q ha hb
    | true =>
      simp only [d13357, d152174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29550 q ha hb
  have h5 (q : Pattern) (ha : d13358 q = 1) (hb : d146836 q = 1) : d152175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13358, d152175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13358, d152175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13359 q = 1) (hb : d146836 q = 1) : d152176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13359, d152176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13359, d152176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13360 q = 1) (hb : d146836 q = 1) : d152177 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13360, d152177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13360, d152177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13283 q = 1) (hb : d146836 q = 1) : d152106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29524 q ha hb
    | true =>
      simp only [d13283, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29521 q ha hb
  have h9 (q : Pattern) (ha : d13284 q = 1) (hb : d146836 q = 1) : d152107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13285 q = 1) (hb : d146836 q = 1) : d152108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5140 q = 1) (hb : d146836 q = 1) : d152110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29521 q ha hb
    | true =>
      simp only [d5140, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29523 q ha hb
  have h12 (q : Pattern) (ha : d5141 q = 1) (hb : d146836 q = 1) : d152111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5142 q = 1) (hb : d146836 q = 1) : d152112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13286 q = 1) (hb : d146836 q = 1) : d152113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13286, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13361 q = 1) (hb : d146836 q = 1) : d152178 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13361, d152178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13361, d152178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13362 q = 1) (hb : d146836 q = 1) : d152179 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13362, d152179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13362, d152179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro29552 (p : Pattern) (ha : d13372 p = 1) (hb : d146836 p = 1) : d152190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d146836 q = 1) : d152180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29551 q ha hb
    | true =>
      simp only [d13363, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d146836 q = 1) : d152181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d146836 q = 1) : d152185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29534 q ha hb
    | true =>
      simp only [d13367, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d146836 q = 1) : d152186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d146836 q = 1) : d152187 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d146836 q = 1) : d152188 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d146836 q = 1) : d152189 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13372 q = 1) (hb : d146836 q = 1) : d152190 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13372, d152190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13372, d152190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29553 (p : Pattern) (ha : d13417 p = 1) (hb : d146836 p = 1) : d152200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29526 q ha hb
    | true =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d146836 q = 1) : d152197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d146836 q = 1) : d152198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d146836 q = 1) : d152199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13417 q = 1) (hb : d146836 q = 1) : d152200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13417, d152200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13417, d152200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29554 (p : Pattern) (ha : d115442 p = 1) (hb : d146836 p = 1) : d152206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d146836 q = 1) : d152157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29544 q ha hb
    | true =>
      simp only [d13331, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29545 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d146836 q = 1) : d152158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d146836 q = 1) : d152159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d146836 q = 1) : d152160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d146836 q = 1) : d152167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29546 q ha hb
    | true =>
      simp only [d13341, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29547 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d146836 q = 1) : d152168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d146836 q = 1) : d152169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d146836 q = 1) : d152195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29552 q ha hb
    | true =>
      simp only [d13377, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29535 q ha hb
  have h9 (q : Pattern) (ha : d115438 q = 1) (hb : d146836 q = 1) : d152196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115438, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d146836 q = 1) : d152201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29553 q ha hb
    | true =>
      simp only [d13418, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d146836 q = 1) : d152202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115439 q = 1) (hb : d146836 q = 1) : d152203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115440 q = 1) (hb : d146836 q = 1) : d152204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115440, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115441 q = 1) (hb : d146836 q = 1) : d152205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115441, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115442 q = 1) (hb : d146836 q = 1) : d152206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d152206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115442, d152206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29555 (p : Pattern) (ha : d13424 p = 1) (hb : d146836 p = 1) : d152207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29526 q ha hb
    | true =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d146836 q = 1) : d152127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d146836 q = 1) : d152153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13424 q = 1) (hb : d146836 q = 1) : d152207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13424, d152207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13424, d152207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29556 (p : Pattern) (ha : d13425 p = 1) (hb : d146836 p = 1) : d152208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d146836 q = 1) : d152131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d146836 q = 1) : d152155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13425 q = 1) (hb : d146836 q = 1) : d152208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13425, d152208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13425, d152208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29557 (p : Pattern) (ha : d13430 p = 1) (hb : d146836 p = 1) : d152213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29526 q ha hb
    | true =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d146836 q = 1) : d152161 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d146836 q = 1) : d152162 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13430 q = 1) (hb : d146836 q = 1) : d152213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13430, d152213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13430, d152213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29558 (p : Pattern) (ha : d13431 p = 1) (hb : d146836 p = 1) : d152214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d146836 q = 1) : d152164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d146836 q = 1) : d152165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13431 q = 1) (hb : d146836 q = 1) : d152214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13431, d152214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13431, d152214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29559 (p : Pattern) (ha : d13435 p = 1) (hb : d146836 p = 1) : d152218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d146836 q = 1) : d152180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29551 q ha hb
    | true =>
      simp only [d13363, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d146836 q = 1) : d152181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d146836 q = 1) : d152185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29534 q ha hb
    | true =>
      simp only [d13367, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d146836 q = 1) : d152186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d146836 q = 1) : d152187 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d146836 q = 1) : d152188 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d146836 q = 1) : d152189 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13435 q = 1) (hb : d146836 q = 1) : d152218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13435, d152218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13435, d152218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29560 (p : Pattern) (ha : d13436 p = 1) (hb : d146836 p = 1) : d152219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d146836 q = 1) : d152185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29534 q ha hb
    | true =>
      simp only [d13367, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d146836 q = 1) : d152186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29527 q ha hb
    | true =>
      simp only [d13298, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d146836 q = 1) : d152191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d146836 q = 1) : d152192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d146836 q = 1) : d152193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13436 q = 1) (hb : d146836 q = 1) : d152219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13436, d152219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13436, d152219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29561 (p : Pattern) (ha : d13442 p = 1) (hb : d146836 p = 1) : d152222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29526 q ha hb
    | true =>
      simp only [d13294, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d146836 q = 1) : d152197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d146836 q = 1) : d152198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d146836 q = 1) : d152199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13442 q = 1) (hb : d146836 q = 1) : d152222 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13442, d152222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13442, d152222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29562 (p : Pattern) (ha : d115447 p = 1) (hb : d146836 p = 1) : d152228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d146836 q = 1) : d152157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29544 q ha hb
    | true =>
      simp only [d13331, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29545 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d146836 q = 1) : d152158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d146836 q = 1) : d152159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d146836 q = 1) : d152160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d146836 q = 1) : d152167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29546 q ha hb
    | true =>
      simp only [d13341, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29547 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d146836 q = 1) : d152168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d146836 q = 1) : d152169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d146836 q = 1) : d152195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29552 q ha hb
    | true =>
      simp only [d13377, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29535 q ha hb
  have h9 (q : Pattern) (ha : d115438 q = 1) (hb : d146836 q = 1) : d152196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115438, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d146836 q = 1) : d152201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29553 q ha hb
    | true =>
      simp only [d13418, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d146836 q = 1) : d152202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115439 q = 1) (hb : d146836 q = 1) : d152203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115440 q = 1) (hb : d146836 q = 1) : d152204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115440, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115441 q = 1) (hb : d146836 q = 1) : d152205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115441, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13426 q = 1) (hb : d146836 q = 1) : d152209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13426, d152209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29555 q ha hb
    | true =>
      simp only [d13426, d152209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29556 q ha hb
  have h16 (q : Pattern) (ha : d13427 q = 1) (hb : d146836 q = 1) : d152210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13427, d152210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13427, d152210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13428 q = 1) (hb : d146836 q = 1) : d152211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13428, d152211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13428, d152211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13429 q = 1) (hb : d146836 q = 1) : d152212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13429, d152212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13429, d152212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13432 q = 1) (hb : d146836 q = 1) : d152215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13432, d152215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29557 q ha hb
    | true =>
      simp only [d13432, d152215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29558 q ha hb
  have h20 (q : Pattern) (ha : d13433 q = 1) (hb : d146836 q = 1) : d152216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13433, d152216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13433, d152216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13434 q = 1) (hb : d146836 q = 1) : d152217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13434, d152217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13434, d152217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13437 q = 1) (hb : d146836 q = 1) : d152220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29559 q ha hb
    | true =>
      simp only [d13437, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29560 q ha hb
  have h23 (q : Pattern) (ha : d115443 q = 1) (hb : d146836 q = 1) : d152221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115443, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13443 q = 1) (hb : d146836 q = 1) : d152223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29561 q ha hb
    | true =>
      simp only [d13443, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13444 q = 1) (hb : d146836 q = 1) : d152224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13444, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115444 q = 1) (hb : d146836 q = 1) : d152225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115444, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115445 q = 1) (hb : d146836 q = 1) : d152226 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115445, d152226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115445, d152226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115446 q = 1) (hb : d146836 q = 1) : d152227 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115446, d152227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115446, d152227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115447 q = 1) (hb : d146836 q = 1) : d152228 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115447, d152228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115447, d152228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29563 (p : Pattern) (ha : d115454 p = 1) (hb : d146836 p = 1) : d152253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13437 q = 1) (hb : d146836 q = 1) : d152220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29559 q ha hb
    | true =>
      simp only [d13437, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29560 q ha hb
  have h2 (q : Pattern) (ha : d115443 q = 1) (hb : d146836 q = 1) : d152221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115443, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13443 q = 1) (hb : d146836 q = 1) : d152223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29561 q ha hb
    | true =>
      simp only [d13443, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13444 q = 1) (hb : d146836 q = 1) : d152224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13444, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115444 q = 1) (hb : d146836 q = 1) : d152225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115444, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115452 q = 1) (hb : d146836 q = 1) : d152251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115452, d152251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115452, d152251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115453 q = 1) (hb : d146836 q = 1) : d152252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115453, d152252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115453, d152252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115454 q = 1) (hb : d146836 q = 1) : d152253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115454, d152253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115454, d152253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29564 (p : Pattern) (ha : d6501 p = 1) (hb : d146836 p = 1) : d152272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6496 q = 1) (hb : d116750 q = 1) : d22538 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d22538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6496, d22538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29522 q ha hb
  have h2 (q : Pattern) (ha : d5134 q = 1) (hb : d116750 q = 1) : d22244 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d22244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29522 q ha hb
    | true =>
      simp only [d5134, d22244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6497 q = 1) (hb : d116750 q = 1) : d22539 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d22539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6497, d22539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5135 q = 1) (hb : d116750 q = 1) : d22245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d22245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5135, d22245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6498 q = 1) (hb : d116750 q = 1) : d22540 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, d22540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6498, d22540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6499 q = 1) (hb : d116750 q = 1) : d22541 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, d22541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6499, d22541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6500 q = 1) (hb : d116750 q = 1) : d22542 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d22542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6500, d22542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6501 q = 1) (hb : d146836 q = 1) : d152272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6501, d146836, d152272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6501, d146836, d152272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29565 (p : Pattern) (ha : d13481 p = 1) (hb : d146836 p = 1) : d149457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d116750 q = 1) : d22497 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d22497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d22497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27985 q ha hb
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d116750 q = 1) : d22313 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d22313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27985 q ha hb
    | true =>
      simp only [d1665, d22313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1854 q = 1) (hb : d116750 q = 1) : d22498 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d22498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1854, d22498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1666 q = 1) (hb : d116750 q = 1) : d22314 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d22314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, d22314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1855 q = 1) (hb : d116750 q = 1) : d22499 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d22499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1855, d22499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1856 q = 1) (hb : d116750 q = 1) : d22500 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d22500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1856, d22500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1857 q = 1) (hb : d116750 q = 1) : d17004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d17004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d17004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
  have h8 (q : Pattern) (ha : d1555 q = 1) (hb : d116750 q = 1) : d10036 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
    | true =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1858 q = 1) (hb : d116750 q = 1) : d17005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d17005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1858, d17005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1556 q = 1) (hb : d116750 q = 1) : d10038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1859 q = 1) (hb : d116750 q = 1) : d17006 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d17006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1859, d17006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1860 q = 1) (hb : d116750 q = 1) : d17007 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d17007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1860, d17007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1861 q = 1) (hb : d116750 q = 1) : d22501 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1861, d22501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1861, d22501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13481 q = 1) (hb : d146836 q = 1) : d149457 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13481, d146836, d149457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13481, d146836, d149457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29566 (p : Pattern) (ha : d13482 p = 1) (hb : d146836 p = 1) : d149461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1857 q = 1) (hb : d116750 q = 1) : d17004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d17004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d17004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d116750 q = 1) : d10036 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
    | true =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1858 q = 1) (hb : d116750 q = 1) : d17005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d17005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1858, d17005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1556 q = 1) (hb : d116750 q = 1) : d10038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1859 q = 1) (hb : d116750 q = 1) : d17006 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d17006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1859, d17006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1860 q = 1) (hb : d116750 q = 1) : d17007 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d17007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1860, d17007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1862 q = 1) (hb : d116750 q = 1) : d22508 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
  have h8 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1863 q = 1) (hb : d116750 q = 1) : d22509 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1863, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1864 q = 1) (hb : d116750 q = 1) : d22510 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1864, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1865 q = 1) (hb : d116750 q = 1) : d22511 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1865, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1866 q = 1) (hb : d116750 q = 1) : d22512 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d22512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1866, d22512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13482 q = 1) (hb : d146836 q = 1) : d149461 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13482, d146836, d149461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13482, d146836, d149461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29567 (p : Pattern) (ha : d13495 p = 1) (hb : d146836 p = 1) : d152264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13486 q = 1) (hb : d116750 q = 1) : d22518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d22518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13486, d22518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29549 q ha hb
  have h2 (q : Pattern) (ha : d10099 q = 1) (hb : d116750 q = 1) : d22324 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d22324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29549 q ha hb
    | true =>
      simp only [d10099, d22324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13487 q = 1) (hb : d116750 q = 1) : d22519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d22519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13487, d22519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10101 q = 1) (hb : d116750 q = 1) : d22325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d22325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10101, d22325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13488 q = 1) (hb : d116750 q = 1) : d22520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, d22520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13488, d22520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13489 q = 1) (hb : d116750 q = 1) : d22521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, d22521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13489, d22521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13493 q = 1) (hb : d116750 q = 1) : d13493 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13494 q = 1) (hb : d116750 q = 1) : d22522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13494, d22522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13494, d22522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13495 q = 1) (hb : d146836 q = 1) : d152264 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13495, d146836, d152264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13495, d146836, d152264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29568 (p : Pattern) (ha : d13505 p = 1) (hb : d146836 p = 1) : d152278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13483 q = 1) (hb : d146836 q = 1) : d152261 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13483, d152261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29565 q ha hb
    | true =>
      simp only [d13483, d152261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29566 q ha hb
  have h2 (q : Pattern) (ha : d13484 q = 1) (hb : d146836 q = 1) : d152262 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13484, d152262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13484, d152262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13485 q = 1) (hb : d146836 q = 1) : d152263 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13485, d152263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13485, d152263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13496 q = 1) (hb : d146836 q = 1) : d152265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13496, d152265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29566 q ha hb
    | true =>
      simp only [d13496, d152265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29567 q ha hb
  have h5 (q : Pattern) (ha : d13497 q = 1) (hb : d146836 q = 1) : d152266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13497, d152266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13497, d152266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13498 q = 1) (hb : d146836 q = 1) : d152267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13498, d152267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13498, d152267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13499 q = 1) (hb : d146836 q = 1) : d152268 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13499, d152268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13499, d152268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13500 q = 1) (hb : d146836 q = 1) : d152269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29566 q ha hb
    | true =>
      simp only [d13500, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29539 q ha hb
  have h9 (q : Pattern) (ha : d13501 q = 1) (hb : d146836 q = 1) : d152270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13502 q = 1) (hb : d146836 q = 1) : d152271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6502 q = 1) (hb : d146836 q = 1) : d152273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29539 q ha hb
    | true =>
      simp only [d6502, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29564 q ha hb
  have h12 (q : Pattern) (ha : d6503 q = 1) (hb : d146836 q = 1) : d152274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6504 q = 1) (hb : d146836 q = 1) : d152275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13503 q = 1) (hb : d146836 q = 1) : d152276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13503, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13504 q = 1) (hb : d146836 q = 1) : d152277 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13504, d152277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13504, d152277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13505 q = 1) (hb : d146836 q = 1) : d152278 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13505, d152278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13505, d152278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro29569 (p : Pattern) (ha : d13509 p = 1) (hb : d146836 p = 1) : d152283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13500 q = 1) (hb : d146836 q = 1) : d152269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29566 q ha hb
    | true =>
      simp only [d13500, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29539 q ha hb
  have h2 (q : Pattern) (ha : d13501 q = 1) (hb : d146836 q = 1) : d152270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13502 q = 1) (hb : d146836 q = 1) : d152271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6502 q = 1) (hb : d146836 q = 1) : d152273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29539 q ha hb
    | true =>
      simp only [d6502, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29564 q ha hb
  have h5 (q : Pattern) (ha : d6503 q = 1) (hb : d146836 q = 1) : d152274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6504 q = 1) (hb : d146836 q = 1) : d152275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13503 q = 1) (hb : d146836 q = 1) : d152276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13503, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6505 q = 1) (hb : d146836 q = 1) : d152281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d152281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6505, d152281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13508 q = 1) (hb : d146836 q = 1) : d152282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13508, d152282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13508, d152282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13509 q = 1) (hb : d146836 q = 1) : d152283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13509, d152283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13509, d152283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro29570 (p : Pattern) (ha : d13515 p = 1) (hb : d146836 p = 1) : d152289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13506 q = 1) (hb : d146836 q = 1) : d152279 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13506, d152279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29568 q ha hb
    | true =>
      simp only [d13506, d152279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13507 q = 1) (hb : d146836 q = 1) : d152280 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13507, d152280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13507, d152280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13510 q = 1) (hb : d146836 q = 1) : d152284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29569 q ha hb
    | true =>
      simp only [d13510, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13511 q = 1) (hb : d146836 q = 1) : d152285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13512 q = 1) (hb : d146836 q = 1) : d152286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13512, d152286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13512, d152286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13513 q = 1) (hb : d146836 q = 1) : d152287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13513, d152287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13513, d152287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13514 q = 1) (hb : d146836 q = 1) : d152288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13514, d152288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13514, d152288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13515 q = 1) (hb : d146836 q = 1) : d152289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13515, d152289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13515, d152289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29571 (p : Pattern) (ha : d13528 p = 1) (hb : d146836 p = 1) : d152301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13510 q = 1) (hb : d146836 q = 1) : d152284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29569 q ha hb
    | true =>
      simp only [d13510, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13511 q = 1) (hb : d146836 q = 1) : d152285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d146836 q = 1) : d152296 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29541 q ha hb
    | true =>
      simp only [d13523, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d146836 q = 1) : d152297 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13525 q = 1) (hb : d146836 q = 1) : d152298 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13525, d152298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13525, d152298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13526 q = 1) (hb : d146836 q = 1) : d152299 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13526, d152299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13526, d152299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13527 q = 1) (hb : d146836 q = 1) : d152300 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13527, d152300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13527, d152300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13528 q = 1) (hb : d146836 q = 1) : d152301 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13528, d152301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13528, d152301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29572 (p : Pattern) (ha : d13569 p = 1) (hb : d146836 p = 1) : d152305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13500 q = 1) (hb : d146836 q = 1) : d152269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29566 q ha hb
    | true =>
      simp only [d13500, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29539 q ha hb
  have h2 (q : Pattern) (ha : d13501 q = 1) (hb : d146836 q = 1) : d152270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13502 q = 1) (hb : d146836 q = 1) : d152271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6502 q = 1) (hb : d146836 q = 1) : d152273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29539 q ha hb
    | true =>
      simp only [d6502, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29564 q ha hb
  have h5 (q : Pattern) (ha : d6503 q = 1) (hb : d146836 q = 1) : d152274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6504 q = 1) (hb : d146836 q = 1) : d152275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13503 q = 1) (hb : d146836 q = 1) : d152276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13503, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13517 q = 1) (hb : d146836 q = 1) : d152290 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29539 q ha hb
    | true =>
      simp only [d13517, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29540 q ha hb
  have h9 (q : Pattern) (ha : d13518 q = 1) (hb : d146836 q = 1) : d152291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13519 q = 1) (hb : d146836 q = 1) : d152292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13520 q = 1) (hb : d146836 q = 1) : d152293 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13520, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13568 q = 1) (hb : d146836 q = 1) : d152304 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13568, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13568, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13569 q = 1) (hb : d146836 q = 1) : d152305 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13569, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13569, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro29573 (p : Pattern) (ha : d13575 p = 1) (hb : d146836 p = 1) : d152311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d146836 q = 1) : d152306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29572 q ha hb
    | true =>
      simp only [d13570, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d146836 q = 1) : d152307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13572 q = 1) (hb : d146836 q = 1) : d152308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13572, d152308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13572, d152308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13573 q = 1) (hb : d146836 q = 1) : d152309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13573, d152309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13573, d152309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13574 q = 1) (hb : d146836 q = 1) : d152310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13574, d152310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13574, d152310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13575 q = 1) (hb : d146836 q = 1) : d152311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13575, d152311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13575, d152311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29574 (p : Pattern) (ha : d115464 p = 1) (hb : d146836 p = 1) : d152317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13529 q = 1) (hb : d146836 q = 1) : d152302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13529, d152302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29570 q ha hb
    | true =>
      simp only [d13529, d152302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29571 q ha hb
  have h2 (q : Pattern) (ha : d115460 q = 1) (hb : d146836 q = 1) : d152303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115460, d152303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115460, d152303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13576 q = 1) (hb : d146836 q = 1) : d152312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13576, d152312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29573 q ha hb
    | true =>
      simp only [d13576, d152312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13577 q = 1) (hb : d146836 q = 1) : d152313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13577, d152313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13577, d152313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115461 q = 1) (hb : d146836 q = 1) : d152314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115461, d152314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115461, d152314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115462 q = 1) (hb : d146836 q = 1) : d152315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115462, d152315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115462, d152315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115463 q = 1) (hb : d146836 q = 1) : d152316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115463, d152316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115463, d152316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115464 q = 1) (hb : d146836 q = 1) : d152317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115464, d152317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115464, d152317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29575 (p : Pattern) (ha : d115470 p = 1) (hb : d146836 p = 1) : d152334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13314 q = 1) (hb : d146836 q = 1) : d152140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13314, d152140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13314, d152140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29530 q ha hb
  have h2 (q : Pattern) (ha : d13315 q = 1) (hb : d146836 q = 1) : d152141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13315, d152141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13315, d152141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13324 q = 1) (hb : d146836 q = 1) : d152150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29530 q ha hb
    | true =>
      simp only [d13324, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29533 q ha hb
  have h4 (q : Pattern) (ha : d13325 q = 1) (hb : d146836 q = 1) : d152151 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13325, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13326 q = 1) (hb : d146836 q = 1) : d152152 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13326, d152152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13326, d152152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115448 q = 1) (hb : d146836 q = 1) : d152229 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115448, d152229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29554 q ha hb
    | true =>
      simp only [d115448, d152229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29562 q ha hb
  have h7 (q : Pattern) (ha : d13467 q = 1) (hb : d146836 q = 1) : d152247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13467, d152247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29536 q ha hb
    | true =>
      simp only [d13467, d152247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29537 q ha hb
  have h8 (q : Pattern) (ha : d115449 q = 1) (hb : d146836 q = 1) : d152248 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115449, d152248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115449, d152248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115450 q = 1) (hb : d146836 q = 1) : d152249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115450, d152249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115450, d152249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115451 q = 1) (hb : d146836 q = 1) : d152250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115451, d152250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115451, d152250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115455 q = 1) (hb : d146836 q = 1) : d152254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115455, d152254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115455, d152254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29563 q ha hb
  have h12 (q : Pattern) (ha : d13476 q = 1) (hb : d146836 q = 1) : d152256 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13476, d152256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13476, d152256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29538 q ha hb
  have h13 (q : Pattern) (ha : d115456 q = 1) (hb : d146836 q = 1) : d152257 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115456, d152257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115456, d152257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115457 q = 1) (hb : d146836 q = 1) : d152258 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115457, d152258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115457, d152258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115458 q = 1) (hb : d146836 q = 1) : d152259 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115458, d152259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115458, d152259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115459 q = 1) (hb : d146836 q = 1) : d152260 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115459, d152260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115459, d152260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115465 q = 1) (hb : d146836 q = 1) : d152318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115465, d152318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115465, d152318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29574 q ha hb
  have h18 (q : Pattern) (ha : d13593 q = 1) (hb : d146836 q = 1) : d152329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13593, d152329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13593, d152329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29543 q ha hb
  have h19 (q : Pattern) (ha : d115466 q = 1) (hb : d146836 q = 1) : d152330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115466, d152330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115466, d152330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115467 q = 1) (hb : d146836 q = 1) : d152331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115467, d152331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115467, d152331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115468 q = 1) (hb : d146836 q = 1) : d152332 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115468, d152332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115468, d152332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115469 q = 1) (hb : d146836 q = 1) : d152333 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115469, d152333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115469, d152333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115470 q = 1) (hb : d146836 q = 1) : d152334 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115470, d152334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115470, d152334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29576 (p : Pattern) (ha : d115476 p = 1) (hb : d146836 p = 1) : d152340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115471 q = 1) (hb : d146836 q = 1) : d152335 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115471, d152335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115471, d152335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29575 q ha hb
  have h2 (q : Pattern) (ha : d115472 q = 1) (hb : d146836 q = 1) : d152336 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115472, d152336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115472, d152336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115473 q = 1) (hb : d146836 q = 1) : d152337 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115473, d152337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115473, d152337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115474 q = 1) (hb : d146836 q = 1) : d152338 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115474, d152338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115474, d152338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115475 q = 1) (hb : d146836 q = 1) : d152339 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115475, d152339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115475, d152339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115476 q = 1) (hb : d146836 q = 1) : d152340 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115476, d152340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115476, d152340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29577 (p : Pattern) (ha : d5237 p = 1) (hb : d146836 p = 1) : d149535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d116750 q = 1) : d10364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
    | true =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2054 q = 1) (hb : d116750 q = 1) : d10366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2055 q = 1) (hb : d116750 q = 1) : d17153 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2056 q = 1) (hb : d116750 q = 1) : d17154 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2056, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2065 q = 1) (hb : d116750 q = 1) : d22688 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
    | true =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2066 q = 1) (hb : d116750 q = 1) : d22689 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2067 q = 1) (hb : d116750 q = 1) : d22690 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d22690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d22690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2068 q = 1) (hb : d116750 q = 1) : d22691 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d22691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2068, d22691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2069 q = 1) (hb : d116750 q = 1) : d22692 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d22692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2069, d22692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5237 q = 1) (hb : d146836 q = 1) : d149535 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5237, d146836, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5237, d146836, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29578 (p : Pattern) (ha : d5246 p = 1) (hb : d116750 p = 1) : d22698 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5242 q = 1) : d5242 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5245 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5246 q = 1) (hb : d116750 q = 1) : d22698 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5246, d116750, d22698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5246, d116750, d22698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro29579 (p : Pattern) (ha : d5252 p = 1) (hb : d146836 p = 1) : d152348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5247 q = 1) (hb : d116750 q = 1) : d22699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d22699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29578 q ha hb
    | true =>
      simp only [d5247, d22699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5248 q = 1) (hb : d116750 q = 1) : d22700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d22700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5248, d22700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5249 q = 1) (hb : d116750 q = 1) : d22701 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5249, d22701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5249, d22701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5250 q = 1) (hb : d116750 q = 1) : d22702 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5250, d22702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5250, d22702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5251 q = 1) (hb : d116750 q = 1) : d22703 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d22703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5251, d22703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5252 q = 1) (hb : d146836 q = 1) : d152348 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5252, d146836, d152348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5252, d146836, d152348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29580 (p : Pattern) (ha : d13609 p = 1) (hb : d146836 p = 1) : d149531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2035 q = 1) (hb : d116750 q = 1) : d10343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20059 q ha hb
    | true =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2036 q = 1) (hb : d116750 q = 1) : d10345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2037 q = 1) (hb : d116750 q = 1) : d17225 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2038 q = 1) (hb : d116750 q = 1) : d17226 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2038, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2053 q = 1) (hb : d116750 q = 1) : d10364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
    | true =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2054 q = 1) (hb : d116750 q = 1) : d10366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2055 q = 1) (hb : d116750 q = 1) : d17153 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2056 q = 1) (hb : d116750 q = 1) : d17154 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2056, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2057 q = 1) (hb : d116750 q = 1) : d22685 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2057, d22685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2057, d22685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13609 q = 1) (hb : d146836 q = 1) : d149531 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13609, d146836, d149531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13609, d146836, d149531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29581 (p : Pattern) (ha : d13614 p = 1) (hb : d146836 p = 1) : d22854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d116750 q = 1) : d22688 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
    | true =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2066 q = 1) (hb : d116750 q = 1) : d22689 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2067 q = 1) (hb : d116750 q = 1) : d22690 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d22690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d22690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2068 q = 1) (hb : d116750 q = 1) : d22691 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d22691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2068, d22691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2071 q = 1) (hb : d116750 q = 1) : d22709 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d22709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, d22709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13614 q = 1) (hb : d146836 q = 1) : d22854 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, d146836, d22854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13614, d146836, d22854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29582 (p : Pattern) (ha : d13620 p = 1) (hb : d146836 p = 1) : d152358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13610 q = 1) (hb : d146836 q = 1) : d152345 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29580 q ha hb
    | true =>
      simp only [d13610, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29577 q ha hb
  have h2 (q : Pattern) (ha : d13611 q = 1) (hb : d146836 q = 1) : d152346 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13612 q = 1) (hb : d146836 q = 1) : d152347 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5253 q = 1) (hb : d146836 q = 1) : d152349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29577 q ha hb
    | true =>
      simp only [d5253, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29579 q ha hb
  have h5 (q : Pattern) (ha : d5254 q = 1) (hb : d146836 q = 1) : d152350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5255 q = 1) (hb : d146836 q = 1) : d152351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13613 q = 1) (hb : d146836 q = 1) : d152352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13613, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13615 q = 1) (hb : d146836 q = 1) : d152353 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29577 q ha hb
    | true =>
      simp only [d13615, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29581 q ha hb
  have h9 (q : Pattern) (ha : d13616 q = 1) (hb : d146836 q = 1) : d152354 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13616, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13617 q = 1) (hb : d146836 q = 1) : d152355 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13617, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13618 q = 1) (hb : d146836 q = 1) : d152356 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13618, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13619 q = 1) (hb : d146836 q = 1) : d152357 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13619, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13619, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13620 q = 1) (hb : d146836 q = 1) : d152358 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13620, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13620, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro29583 (p : Pattern) (ha : d13624 p = 1) (hb : d146836 p = 1) : d152362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13615 q = 1) (hb : d146836 q = 1) : d152353 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29577 q ha hb
    | true =>
      simp only [d13615, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29581 q ha hb
  have h2 (q : Pattern) (ha : d13616 q = 1) (hb : d146836 q = 1) : d152354 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13616, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13617 q = 1) (hb : d146836 q = 1) : d152355 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13617, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13618 q = 1) (hb : d146836 q = 1) : d152356 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13618, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13623 q = 1) (hb : d146836 q = 1) : d152361 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13623, d152361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13623, d152361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13624 q = 1) (hb : d146836 q = 1) : d152362 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13624, d152362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13624, d152362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29584 (p : Pattern) (ha : d13630 p = 1) (hb : d146836 p = 1) : d152368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29582 q ha hb
    | true =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d146836 q = 1) : d152366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13629 q = 1) (hb : d146836 q = 1) : d152367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13629, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13630 q = 1) (hb : d146836 q = 1) : d152368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13630, d152368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13630, d152368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29585 (p : Pattern) (ha : d13634 p = 1) (hb : d146836 p = 1) : d152372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d146836 q = 1) : d152370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d146836 q = 1) : d152371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13634 q = 1) (hb : d146836 q = 1) : d152372 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13634, d152372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13634, d152372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29586 (p : Pattern) (ha : d13640 p = 1) (hb : d146836 p = 1) : d152378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13635 q = 1) (hb : d146836 q = 1) : d152373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29584 q ha hb
    | true =>
      simp only [d13635, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29585 q ha hb
  have h2 (q : Pattern) (ha : d13636 q = 1) (hb : d146836 q = 1) : d152374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13637 q = 1) (hb : d146836 q = 1) : d152375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13637, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13638 q = 1) (hb : d146836 q = 1) : d152376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13639 q = 1) (hb : d146836 q = 1) : d152377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13640 q = 1) (hb : d146836 q = 1) : d152378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13640, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13640, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29587 (p : Pattern) (ha : d13643 p = 1) (hb : d146836 p = 1) : d152381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29582 q ha hb
    | true =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d146836 q = 1) : d152366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13629 q = 1) (hb : d146836 q = 1) : d152367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13629, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13643 q = 1) (hb : d146836 q = 1) : d152381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13643, d152381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13643, d152381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29588 (p : Pattern) (ha : d13644 p = 1) (hb : d146836 p = 1) : d152382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d146836 q = 1) : d152370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d146836 q = 1) : d152371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13644 q = 1) (hb : d146836 q = 1) : d152382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13644, d152382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13644, d152382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29589 (p : Pattern) (ha : d13650 p = 1) (hb : d146836 p = 1) : d152388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13635 q = 1) (hb : d146836 q = 1) : d152373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29584 q ha hb
    | true =>
      simp only [d13635, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29585 q ha hb
  have h2 (q : Pattern) (ha : d13636 q = 1) (hb : d146836 q = 1) : d152374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13637 q = 1) (hb : d146836 q = 1) : d152375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13637, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13638 q = 1) (hb : d146836 q = 1) : d152376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13639 q = 1) (hb : d146836 q = 1) : d152377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13645 q = 1) (hb : d146836 q = 1) : d152383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29587 q ha hb
    | true =>
      simp only [d13645, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29588 q ha hb
  have h7 (q : Pattern) (ha : d13646 q = 1) (hb : d146836 q = 1) : d152384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13647 q = 1) (hb : d146836 q = 1) : d152385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13647, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13648 q = 1) (hb : d146836 q = 1) : d152386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13649 q = 1) (hb : d146836 q = 1) : d152387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13650 q = 1) (hb : d146836 q = 1) : d152388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13650, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13650, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29590 (p : Pattern) (ha : d13693 p = 1) (hb : d146836 p = 1) : d152422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13610 q = 1) (hb : d146836 q = 1) : d152345 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29580 q ha hb
    | true =>
      simp only [d13610, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29577 q ha hb
  have h2 (q : Pattern) (ha : d13611 q = 1) (hb : d146836 q = 1) : d152346 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13612 q = 1) (hb : d146836 q = 1) : d152347 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5253 q = 1) (hb : d146836 q = 1) : d152349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29577 q ha hb
    | true =>
      simp only [d5253, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29579 q ha hb
  have h5 (q : Pattern) (ha : d5254 q = 1) (hb : d146836 q = 1) : d152350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5255 q = 1) (hb : d146836 q = 1) : d152351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13613 q = 1) (hb : d146836 q = 1) : d152352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13613, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5256 q = 1) (hb : d146836 q = 1) : d152420 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d152420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5256, d152420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13692 q = 1) (hb : d146836 q = 1) : d152421 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13692, d152421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13692, d152421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13693 q = 1) (hb : d146836 q = 1) : d152422 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13693, d152422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13693, d152422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro29591 (p : Pattern) (ha : d13703 p = 1) (hb : d146836 p = 1) : d152432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d146836 q = 1) : d152423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29590 q ha hb
    | true =>
      simp only [d13694, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d146836 q = 1) : d152424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13700 q = 1) (hb : d146836 q = 1) : d152429 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13701 q = 1) (hb : d146836 q = 1) : d152430 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13701, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13702 q = 1) (hb : d146836 q = 1) : d152431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13702, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13703 q = 1) (hb : d146836 q = 1) : d152432 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13703, d152432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13703, d152432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29592 (p : Pattern) (ha : d13787 p = 1) (hb : d146836 p = 1) : d152478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13777 q = 1) (hb : d146836 q = 1) : d152468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13777, d152468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29591 q ha hb
    | true =>
      simp only [d13777, d152468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29585 q ha hb
  have h2 (q : Pattern) (ha : d13778 q = 1) (hb : d146836 q = 1) : d152469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13778, d152469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13778, d152469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13779 q = 1) (hb : d146836 q = 1) : d152470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13779, d152470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13779, d152470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13780 q = 1) (hb : d146836 q = 1) : d152471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13780, d152471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13780, d152471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13781 q = 1) (hb : d146836 q = 1) : d152472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13781, d152472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13781, d152472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13782 q = 1) (hb : d146836 q = 1) : d152473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29585 q ha hb
    | true =>
      simp only [d13782, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13783 q = 1) (hb : d146836 q = 1) : d152474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13784 q = 1) (hb : d146836 q = 1) : d152475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13784, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13785 q = 1) (hb : d146836 q = 1) : d152476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13786 q = 1) (hb : d146836 q = 1) : d152477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13787 q = 1) (hb : d146836 q = 1) : d152478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13787, d152478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13787, d152478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29593 (p : Pattern) (ha : d13793 p = 1) (hb : d146836 p = 1) : d152484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13782 q = 1) (hb : d146836 q = 1) : d152473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29585 q ha hb
    | true =>
      simp only [d13782, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13783 q = 1) (hb : d146836 q = 1) : d152474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13784 q = 1) (hb : d146836 q = 1) : d152475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13784, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13785 q = 1) (hb : d146836 q = 1) : d152476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13786 q = 1) (hb : d146836 q = 1) : d152477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13788 q = 1) (hb : d146836 q = 1) : d152479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29588 q ha hb
    | true =>
      simp only [d13788, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13789 q = 1) (hb : d146836 q = 1) : d152480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13790 q = 1) (hb : d146836 q = 1) : d152481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13790, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13791 q = 1) (hb : d146836 q = 1) : d152482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13792 q = 1) (hb : d146836 q = 1) : d152483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13793 q = 1) (hb : d146836 q = 1) : d152484 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13793, d152484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13793, d152484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29594 (p : Pattern) (ha : d13802 p = 1) (hb : d146836 p = 1) : d152493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13788 q = 1) (hb : d146836 q = 1) : d152479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29588 q ha hb
    | true =>
      simp only [d13788, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13789 q = 1) (hb : d146836 q = 1) : d152480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13790 q = 1) (hb : d146836 q = 1) : d152481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13790, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13791 q = 1) (hb : d146836 q = 1) : d152482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13792 q = 1) (hb : d146836 q = 1) : d152483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13802 q = 1) (hb : d146836 q = 1) : d152493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13802, d152493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13802, d152493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29595 (p : Pattern) (ha : d6642 p = 1) (hb : d146836 p = 1) : d149675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d116750 q = 1) : d17376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d17376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d17376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d116750 q = 1) : d10364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
    | true =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2341 q = 1) (hb : d116750 q = 1) : d17377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d17377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2341, d17377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2054 q = 1) (hb : d116750 q = 1) : d10366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2342 q = 1) (hb : d116750 q = 1) : d17378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d17378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2342, d17378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2343 q = 1) (hb : d116750 q = 1) : d17379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d17379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2343, d17379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2346 q = 1) (hb : d116750 q = 1) : d22943 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d22943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d22943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
  have h8 (q : Pattern) (ha : d2065 q = 1) (hb : d116750 q = 1) : d22688 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
    | true =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2347 q = 1) (hb : d116750 q = 1) : d22944 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d22944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2347, d22944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2066 q = 1) (hb : d116750 q = 1) : d22689 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2348 q = 1) (hb : d116750 q = 1) : d22945 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d22945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2348, d22945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2349 q = 1) (hb : d116750 q = 1) : d22946 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d22946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2349, d22946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2350 q = 1) (hb : d116750 q = 1) : d22947 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d22947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2350, d22947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6642 q = 1) (hb : d146836 q = 1) : d149675 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6642, d146836, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6642, d146836, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29596 (p : Pattern) (ha : d13843 p = 1) (hb : d146836 p = 1) : d23045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d116750 q = 1) : d22943 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d22943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d22943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d116750 q = 1) : d22688 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20030 q ha hb
    | true =>
      simp only [d2065, d22688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2347 q = 1) (hb : d116750 q = 1) : d22944 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d22944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2347, d22944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2066 q = 1) (hb : d116750 q = 1) : d22689 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d22689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2348 q = 1) (hb : d116750 q = 1) : d22945 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d22945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2348, d22945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2349 q = 1) (hb : d116750 q = 1) : d22946 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d22946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2349, d22946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2355 q = 1) (hb : d116750 q = 1) : d22975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d22975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2355, d22975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13843 q = 1) (hb : d146836 q = 1) : d23045 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, d146836, d23045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13843, d146836, d23045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29597 (p : Pattern) (ha : d13849 p = 1) (hb : d146836 p = 1) : d152532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13844 q = 1) (hb : d146836 q = 1) : d152527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29595 q ha hb
    | true =>
      simp only [d13844, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29596 q ha hb
  have h2 (q : Pattern) (ha : d13845 q = 1) (hb : d146836 q = 1) : d152528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13845, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13846 q = 1) (hb : d146836 q = 1) : d152529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13846, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13847 q = 1) (hb : d146836 q = 1) : d152530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13847, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13848 q = 1) (hb : d146836 q = 1) : d152531 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13848, d152531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13848, d152531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13849 q = 1) (hb : d146836 q = 1) : d152532 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13849, d152532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13849, d152532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29598 (p : Pattern) (ha : d13913 p = 1) (hb : d146836 p = 1) : d152559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13850 q = 1) (hb : d146836 q = 1) : d152533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29597 q ha hb
    | true =>
      simp only [d13850, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13851 q = 1) (hb : d146836 q = 1) : d152534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13910 q = 1) (hb : d146836 q = 1) : d152556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13910, d152556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13910, d152556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13911 q = 1) (hb : d146836 q = 1) : d152557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13911, d152557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13911, d152557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13912 q = 1) (hb : d146836 q = 1) : d152558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13912, d152558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13912, d152558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13913 q = 1) (hb : d146836 q = 1) : d152559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13913, d152559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13913, d152559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29599 (p : Pattern) (ha : d13919 p = 1) (hb : d146836 p = 1) : d152565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13914 q = 1) (hb : d146836 q = 1) : d152560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13914, d152560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29598 q ha hb
    | true =>
      simp only [d13914, d152560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13915 q = 1) (hb : d146836 q = 1) : d152561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13915, d152561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13915, d152561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13916 q = 1) (hb : d146836 q = 1) : d152562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13916, d152562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13916, d152562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13917 q = 1) (hb : d146836 q = 1) : d152563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13917, d152563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13917, d152563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13918 q = 1) (hb : d146836 q = 1) : d152564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13918, d152564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13918, d152564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13919 q = 1) (hb : d146836 q = 1) : d152565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13919, d152565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13919, d152565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29600 (p : Pattern) (ha : d13655 p = 1) (hb : d146836 p = 1) : d152393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29582 q ha hb
    | true =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d146836 q = 1) : d152366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13654 q = 1) (hb : d146836 q = 1) : d152392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13655 q = 1) (hb : d146836 q = 1) : d152393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13655, d152393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13655, d152393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29601 (p : Pattern) (ha : d13657 p = 1) (hb : d146836 p = 1) : d152395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d146836 q = 1) : d152370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d146836 q = 1) : d152394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13657 q = 1) (hb : d146836 q = 1) : d152395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13657, d152395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13657, d152395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29602 (p : Pattern) (ha : d13664 p = 1) (hb : d146836 p = 1) : d152402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29582 q ha hb
    | true =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13662 q = 1) (hb : d146836 q = 1) : d152400 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13663 q = 1) (hb : d146836 q = 1) : d152401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13663, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13664 q = 1) (hb : d146836 q = 1) : d152402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13664, d152402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13664, d152402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29603 (p : Pattern) (ha : d13667 p = 1) (hb : d146836 p = 1) : d152405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d146836 q = 1) : d152403 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d146836 q = 1) : d152404 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13667 q = 1) (hb : d146836 q = 1) : d152405 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13667, d152405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13667, d152405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29604 (p : Pattern) (ha : d13671 p = 1) (hb : d146836 p = 1) : d149593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2144 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28034 q ha hb
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2145 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2146 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2147 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2035 q = 1) (hb : d116750 q = 1) : d10343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20059 q ha hb
    | true =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2036 q = 1) (hb : d116750 q = 1) : d10345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2037 q = 1) (hb : d116750 q = 1) : d17225 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2038 q = 1) (hb : d116750 q = 1) : d17226 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2038, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2148 q = 1) (hb : d116750 q = 1) : d22767 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2148, d22767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2148, d22767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13671 q = 1) (hb : d146836 q = 1) : d149593 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13671, d146836, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13671, d146836, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29605 (p : Pattern) (ha : d13689 p = 1) (hb : d146836 p = 1) : d152417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13672 q = 1) (hb : d146836 q = 1) : d152409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13672, d152409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29604 q ha hb
    | true =>
      simp only [d13672, d152409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29580 q ha hb
  have h2 (q : Pattern) (ha : d13673 q = 1) (hb : d146836 q = 1) : d152410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13673, d152410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13673, d152410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13674 q = 1) (hb : d146836 q = 1) : d152411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13674, d152411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13674, d152411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13683 q = 1) (hb : d146836 q = 1) : d13683 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13684 q = 1) (hb : d146836 q = 1) : d152412 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13684, d152412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29580 q ha hb
    | true =>
      simp only [d13684, d152412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13685 q = 1) (hb : d146836 q = 1) : d152413 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13685, d152413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13685, d152413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13686 q = 1) (hb : d146836 q = 1) : d152414 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13686, d152414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13686, d152414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13687 q = 1) (hb : d146836 q = 1) : d152415 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13687, d152415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13687, d152415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13610 q = 1) (hb : d146836 q = 1) : d152345 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29580 q ha hb
    | true =>
      simp only [d13610, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29577 q ha hb
  have h10 (q : Pattern) (ha : d13611 q = 1) (hb : d146836 q = 1) : d152346 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13612 q = 1) (hb : d146836 q = 1) : d152347 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5253 q = 1) (hb : d146836 q = 1) : d152349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29577 q ha hb
    | true =>
      simp only [d5253, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29579 q ha hb
  have h13 (q : Pattern) (ha : d5254 q = 1) (hb : d146836 q = 1) : d152350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5255 q = 1) (hb : d146836 q = 1) : d152351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13613 q = 1) (hb : d146836 q = 1) : d152352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13613, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13688 q = 1) (hb : d146836 q = 1) : d152416 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13688, d152416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13688, d152416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13689 q = 1) (hb : d146836 q = 1) : d152417 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13689, d152417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13689, d152417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro29606 (p : Pattern) (ha : d13699 p = 1) (hb : d146836 p = 1) : d152428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d146836 q = 1) : d152418 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29605 q ha hb
    | true =>
      simp only [d13690, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d146836 q = 1) : d152419 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d146836 q = 1) : d152423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29590 q ha hb
    | true =>
      simp only [d13694, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d146836 q = 1) : d152424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d146836 q = 1) : d152425 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d146836 q = 1) : d152426 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d146836 q = 1) : d152427 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13699 q = 1) (hb : d146836 q = 1) : d152428 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13699, d152428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13699, d152428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29607 (p : Pattern) (ha : d13744 p = 1) (hb : d146836 p = 1) : d152438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29582 q ha hb
    | true =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d146836 q = 1) : d152435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d146836 q = 1) : d152436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d146836 q = 1) : d152437 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13744 q = 1) (hb : d146836 q = 1) : d152438 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13744, d152438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13744, d152438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29608 (p : Pattern) (ha : d115485 p = 1) (hb : d146836 p = 1) : d152444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13658 q = 1) (hb : d146836 q = 1) : d152396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29600 q ha hb
    | true =>
      simp only [d13658, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29601 q ha hb
  have h2 (q : Pattern) (ha : d13659 q = 1) (hb : d146836 q = 1) : d152397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13660 q = 1) (hb : d146836 q = 1) : d152398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13660, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13661 q = 1) (hb : d146836 q = 1) : d152399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13668 q = 1) (hb : d146836 q = 1) : d152406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29602 q ha hb
    | true =>
      simp only [d13668, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29603 q ha hb
  have h6 (q : Pattern) (ha : d13669 q = 1) (hb : d146836 q = 1) : d152407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13670 q = 1) (hb : d146836 q = 1) : d152408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13670, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13704 q = 1) (hb : d146836 q = 1) : d152433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29606 q ha hb
    | true =>
      simp only [d13704, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29591 q ha hb
  have h9 (q : Pattern) (ha : d115481 q = 1) (hb : d146836 q = 1) : d152434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115481, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13745 q = 1) (hb : d146836 q = 1) : d152439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29607 q ha hb
    | true =>
      simp only [d13745, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13746 q = 1) (hb : d146836 q = 1) : d152440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13746, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115482 q = 1) (hb : d146836 q = 1) : d152441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115482, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115483 q = 1) (hb : d146836 q = 1) : d152442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115483, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115484 q = 1) (hb : d146836 q = 1) : d152443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115484, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115485 q = 1) (hb : d146836 q = 1) : d152444 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115485, d152444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115485, d152444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29609 (p : Pattern) (ha : d13751 p = 1) (hb : d146836 p = 1) : d152445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29582 q ha hb
    | true =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d146836 q = 1) : d152366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13654 q = 1) (hb : d146836 q = 1) : d152392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13751 q = 1) (hb : d146836 q = 1) : d152445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13751, d152445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13751, d152445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29610 (p : Pattern) (ha : d13752 p = 1) (hb : d146836 p = 1) : d152446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d146836 q = 1) : d152370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d146836 q = 1) : d152394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13752 q = 1) (hb : d146836 q = 1) : d152446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13752, d152446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13752, d152446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29611 (p : Pattern) (ha : d13757 p = 1) (hb : d146836 p = 1) : d152451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29582 q ha hb
    | true =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13662 q = 1) (hb : d146836 q = 1) : d152400 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13663 q = 1) (hb : d146836 q = 1) : d152401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13663, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13757 q = 1) (hb : d146836 q = 1) : d152451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13757, d152451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13757, d152451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29612 (p : Pattern) (ha : d13758 p = 1) (hb : d146836 p = 1) : d152452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d146836 q = 1) : d152403 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d146836 q = 1) : d152404 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13758 q = 1) (hb : d146836 q = 1) : d152452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13758, d152452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13758, d152452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29613 (p : Pattern) (ha : d13762 p = 1) (hb : d146836 p = 1) : d152456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d146836 q = 1) : d152418 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29605 q ha hb
    | true =>
      simp only [d13690, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d146836 q = 1) : d152419 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d146836 q = 1) : d152423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29590 q ha hb
    | true =>
      simp only [d13694, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d146836 q = 1) : d152424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d146836 q = 1) : d152425 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d146836 q = 1) : d152426 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d146836 q = 1) : d152427 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13762 q = 1) (hb : d146836 q = 1) : d152456 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13762, d152456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13762, d152456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29614 (p : Pattern) (ha : d13763 p = 1) (hb : d146836 p = 1) : d152457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d146836 q = 1) : d152423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29590 q ha hb
    | true =>
      simp only [d13694, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d146836 q = 1) : d152424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29583 q ha hb
    | true =>
      simp only [d13625, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13700 q = 1) (hb : d146836 q = 1) : d152429 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13701 q = 1) (hb : d146836 q = 1) : d152430 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13701, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13702 q = 1) (hb : d146836 q = 1) : d152431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13702, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13763 q = 1) (hb : d146836 q = 1) : d152457 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13763, d152457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13763, d152457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29615 (p : Pattern) (ha : d13769 p = 1) (hb : d146836 p = 1) : d152460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29582 q ha hb
    | true =>
      simp only [d13621, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d146836 q = 1) : d152435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d146836 q = 1) : d152436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d146836 q = 1) : d152437 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13769 q = 1) (hb : d146836 q = 1) : d152460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13769, d152460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13769, d152460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29616 (p : Pattern) (ha : d115490 p = 1) (hb : d146836 p = 1) : d152466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13658 q = 1) (hb : d146836 q = 1) : d152396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29600 q ha hb
    | true =>
      simp only [d13658, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29601 q ha hb
  have h2 (q : Pattern) (ha : d13659 q = 1) (hb : d146836 q = 1) : d152397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13660 q = 1) (hb : d146836 q = 1) : d152398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13660, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13661 q = 1) (hb : d146836 q = 1) : d152399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13668 q = 1) (hb : d146836 q = 1) : d152406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29602 q ha hb
    | true =>
      simp only [d13668, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29603 q ha hb
  have h6 (q : Pattern) (ha : d13669 q = 1) (hb : d146836 q = 1) : d152407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13670 q = 1) (hb : d146836 q = 1) : d152408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13670, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13704 q = 1) (hb : d146836 q = 1) : d152433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29606 q ha hb
    | true =>
      simp only [d13704, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29591 q ha hb
  have h9 (q : Pattern) (ha : d115481 q = 1) (hb : d146836 q = 1) : d152434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115481, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13745 q = 1) (hb : d146836 q = 1) : d152439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29607 q ha hb
    | true =>
      simp only [d13745, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13746 q = 1) (hb : d146836 q = 1) : d152440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13746, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115482 q = 1) (hb : d146836 q = 1) : d152441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115482, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115483 q = 1) (hb : d146836 q = 1) : d152442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115483, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115484 q = 1) (hb : d146836 q = 1) : d152443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115484, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13753 q = 1) (hb : d146836 q = 1) : d152447 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13753, d152447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29609 q ha hb
    | true =>
      simp only [d13753, d152447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29610 q ha hb
  have h16 (q : Pattern) (ha : d13754 q = 1) (hb : d146836 q = 1) : d152448 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13754, d152448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13754, d152448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13755 q = 1) (hb : d146836 q = 1) : d152449 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13755, d152449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13755, d152449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13756 q = 1) (hb : d146836 q = 1) : d152450 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13756, d152450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13756, d152450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13759 q = 1) (hb : d146836 q = 1) : d152453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13759, d152453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29611 q ha hb
    | true =>
      simp only [d13759, d152453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29612 q ha hb
  have h20 (q : Pattern) (ha : d13760 q = 1) (hb : d146836 q = 1) : d152454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13760, d152454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13760, d152454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13761 q = 1) (hb : d146836 q = 1) : d152455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13761, d152455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13761, d152455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13764 q = 1) (hb : d146836 q = 1) : d152458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29613 q ha hb
    | true =>
      simp only [d13764, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29614 q ha hb
  have h23 (q : Pattern) (ha : d115486 q = 1) (hb : d146836 q = 1) : d152459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115486, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13770 q = 1) (hb : d146836 q = 1) : d152461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29615 q ha hb
    | true =>
      simp only [d13770, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13771 q = 1) (hb : d146836 q = 1) : d152462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13771, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115487 q = 1) (hb : d146836 q = 1) : d152463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115487, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115488 q = 1) (hb : d146836 q = 1) : d152464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115488, d152464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115488, d152464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115489 q = 1) (hb : d146836 q = 1) : d152465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115489, d152465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115489, d152465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115490 q = 1) (hb : d146836 q = 1) : d152466 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115490, d152466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115490, d152466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29617 (p : Pattern) (ha : d115497 p = 1) (hb : d146836 p = 1) : d152491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13764 q = 1) (hb : d146836 q = 1) : d152458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29613 q ha hb
    | true =>
      simp only [d13764, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29614 q ha hb
  have h2 (q : Pattern) (ha : d115486 q = 1) (hb : d146836 q = 1) : d152459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115486, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13770 q = 1) (hb : d146836 q = 1) : d152461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29615 q ha hb
    | true =>
      simp only [d13770, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13771 q = 1) (hb : d146836 q = 1) : d152462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13771, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115487 q = 1) (hb : d146836 q = 1) : d152463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115487, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115495 q = 1) (hb : d146836 q = 1) : d152489 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115495, d152489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115495, d152489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115496 q = 1) (hb : d146836 q = 1) : d152490 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115496, d152490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115496, d152490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115497 q = 1) (hb : d146836 q = 1) : d152491 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115497, d152491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115497, d152491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29618 (p : Pattern) (ha : d6648 p = 1) (hb : d146836 p = 1) : d152509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6643 q = 1) (hb : d116750 q = 1) : d22952 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d22952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d22952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29578 q ha hb
  have h2 (q : Pattern) (ha : d5247 q = 1) (hb : d116750 q = 1) : d22699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d22699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29578 q ha hb
    | true =>
      simp only [d5247, d22699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6644 q = 1) (hb : d116750 q = 1) : d22953 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d22953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6644, d22953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5248 q = 1) (hb : d116750 q = 1) : d22700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d22700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5248, d22700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6645 q = 1) (hb : d116750 q = 1) : d22954 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, d22954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6645, d22954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6646 q = 1) (hb : d116750 q = 1) : d22955 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, d22955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6646, d22955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6647 q = 1) (hb : d116750 q = 1) : d22956 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d22956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6647, d22956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6648 q = 1) (hb : d146836 q = 1) : d152509 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6648, d146836, d152509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6648, d146836, d152509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29619 (p : Pattern) (ha : d13808 p = 1) (hb : d146836 p = 1) : d149666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28034 q ha hb
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28034 q ha hb
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2332 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2145 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2333 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2334 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2335 q = 1) (hb : d116750 q = 1) : d17369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d17369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d17369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20059 q ha hb
  have h8 (q : Pattern) (ha : d2035 q = 1) (hb : d116750 q = 1) : d10343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20059 q ha hb
    | true =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2336 q = 1) (hb : d116750 q = 1) : d17370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d17370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2336, d17370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2036 q = 1) (hb : d116750 q = 1) : d10345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2337 q = 1) (hb : d116750 q = 1) : d17371 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d17371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2337, d17371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2338 q = 1) (hb : d116750 q = 1) : d17372 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d17372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2338, d17372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2339 q = 1) (hb : d116750 q = 1) : d22930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2339, d22930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2339, d22930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13808 q = 1) (hb : d146836 q = 1) : d149666 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13808, d146836, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13808, d146836, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29620 (p : Pattern) (ha : d13809 p = 1) (hb : d146836 p = 1) : d149670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2335 q = 1) (hb : d116750 q = 1) : d17369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d17369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d17369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20059 q ha hb
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d116750 q = 1) : d10343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20059 q ha hb
    | true =>
      simp only [d2035, d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2336 q = 1) (hb : d116750 q = 1) : d17370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d17370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2336, d17370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2036 q = 1) (hb : d116750 q = 1) : d10345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2337 q = 1) (hb : d116750 q = 1) : d17371 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d17371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2337, d17371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2338 q = 1) (hb : d116750 q = 1) : d17372 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d17372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2338, d17372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2340 q = 1) (hb : d116750 q = 1) : d17376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d17376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d17376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
  have h8 (q : Pattern) (ha : d2053 q = 1) (hb : d116750 q = 1) : d10364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20043 q ha hb
    | true =>
      simp only [d2053, d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2341 q = 1) (hb : d116750 q = 1) : d17377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d17377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2341, d17377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2054 q = 1) (hb : d116750 q = 1) : d10366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2054, d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2342 q = 1) (hb : d116750 q = 1) : d17378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d17378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2342, d17378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2343 q = 1) (hb : d116750 q = 1) : d17379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d17379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2343, d17379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2344 q = 1) (hb : d116750 q = 1) : d22932 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, d22932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2344, d22932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13809 q = 1) (hb : d146836 q = 1) : d149670 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13809, d146836, d149670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13809, d146836, d149670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29621 (p : Pattern) (ha : d13832 p = 1) (hb : d146836 p = 1) : d152515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13810 q = 1) (hb : d146836 q = 1) : d152499 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13810, d152499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29619 q ha hb
    | true =>
      simp only [d13810, d152499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29620 q ha hb
  have h2 (q : Pattern) (ha : d13811 q = 1) (hb : d146836 q = 1) : d152500 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13811, d152500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13811, d152500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13812 q = 1) (hb : d146836 q = 1) : d152501 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13812, d152501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13812, d152501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13822 q = 1) (hb : d146836 q = 1) : d13822 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13823 q = 1) (hb : d146836 q = 1) : d152502 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13823, d152502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29620 q ha hb
    | true =>
      simp only [d13823, d152502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13824 q = 1) (hb : d146836 q = 1) : d152503 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13824, d152503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13824, d152503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13825 q = 1) (hb : d146836 q = 1) : d152504 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13825, d152504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13825, d152504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13826 q = 1) (hb : d146836 q = 1) : d152505 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13826, d152505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13826, d152505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13827 q = 1) (hb : d146836 q = 1) : d152506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29620 q ha hb
    | true =>
      simp only [d13827, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29595 q ha hb
  have h10 (q : Pattern) (ha : d13828 q = 1) (hb : d146836 q = 1) : d152507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13829 q = 1) (hb : d146836 q = 1) : d152508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6649 q = 1) (hb : d146836 q = 1) : d152510 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29595 q ha hb
    | true =>
      simp only [d6649, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29618 q ha hb
  have h13 (q : Pattern) (ha : d6650 q = 1) (hb : d146836 q = 1) : d152511 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6651 q = 1) (hb : d146836 q = 1) : d152512 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13830 q = 1) (hb : d146836 q = 1) : d152513 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13830, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13831 q = 1) (hb : d146836 q = 1) : d152514 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13831, d152514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13831, d152514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13832 q = 1) (hb : d146836 q = 1) : d152515 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13832, d152515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13832, d152515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro29622 (p : Pattern) (ha : d13836 p = 1) (hb : d146836 p = 1) : d152520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13827 q = 1) (hb : d146836 q = 1) : d152506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29620 q ha hb
    | true =>
      simp only [d13827, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29595 q ha hb
  have h2 (q : Pattern) (ha : d13828 q = 1) (hb : d146836 q = 1) : d152507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13829 q = 1) (hb : d146836 q = 1) : d152508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6649 q = 1) (hb : d146836 q = 1) : d152510 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29595 q ha hb
    | true =>
      simp only [d6649, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29618 q ha hb
  have h5 (q : Pattern) (ha : d6650 q = 1) (hb : d146836 q = 1) : d152511 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6651 q = 1) (hb : d146836 q = 1) : d152512 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13830 q = 1) (hb : d146836 q = 1) : d152513 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13830, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6652 q = 1) (hb : d146836 q = 1) : d152518 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d152518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6652, d152518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13835 q = 1) (hb : d146836 q = 1) : d152519 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13835, d152519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13835, d152519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13836 q = 1) (hb : d146836 q = 1) : d152520 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13836, d152520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13836, d152520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro29623 (p : Pattern) (ha : d13842 p = 1) (hb : d146836 p = 1) : d152526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13833 q = 1) (hb : d146836 q = 1) : d152516 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13833, d152516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29621 q ha hb
    | true =>
      simp only [d13833, d152516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13834 q = 1) (hb : d146836 q = 1) : d152517 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13834, d152517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13834, d152517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13837 q = 1) (hb : d146836 q = 1) : d152521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29622 q ha hb
    | true =>
      simp only [d13837, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13838 q = 1) (hb : d146836 q = 1) : d152522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13839 q = 1) (hb : d146836 q = 1) : d152523 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13839, d152523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13839, d152523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13840 q = 1) (hb : d146836 q = 1) : d152524 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13840, d152524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13840, d152524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13841 q = 1) (hb : d146836 q = 1) : d152525 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13841, d152525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13841, d152525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13842 q = 1) (hb : d146836 q = 1) : d152526 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13842, d152526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13842, d152526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29624 (p : Pattern) (ha : d13855 p = 1) (hb : d146836 p = 1) : d152538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13837 q = 1) (hb : d146836 q = 1) : d152521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29622 q ha hb
    | true =>
      simp only [d13837, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13838 q = 1) (hb : d146836 q = 1) : d152522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d146836 q = 1) : d152533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29597 q ha hb
    | true =>
      simp only [d13850, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d146836 q = 1) : d152534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13852 q = 1) (hb : d146836 q = 1) : d152535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13852, d152535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13852, d152535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13853 q = 1) (hb : d146836 q = 1) : d152536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13853, d152536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13853, d152536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13854 q = 1) (hb : d146836 q = 1) : d152537 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13854, d152537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13854, d152537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13855 q = 1) (hb : d146836 q = 1) : d152538 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13855, d152538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13855, d152538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29625 (p : Pattern) (ha : d13896 p = 1) (hb : d146836 p = 1) : d152542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13827 q = 1) (hb : d146836 q = 1) : d152506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29620 q ha hb
    | true =>
      simp only [d13827, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29595 q ha hb
  have h2 (q : Pattern) (ha : d13828 q = 1) (hb : d146836 q = 1) : d152507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13829 q = 1) (hb : d146836 q = 1) : d152508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6649 q = 1) (hb : d146836 q = 1) : d152510 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29595 q ha hb
    | true =>
      simp only [d6649, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29618 q ha hb
  have h5 (q : Pattern) (ha : d6650 q = 1) (hb : d146836 q = 1) : d152511 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6651 q = 1) (hb : d146836 q = 1) : d152512 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13830 q = 1) (hb : d146836 q = 1) : d152513 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13830, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13844 q = 1) (hb : d146836 q = 1) : d152527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29595 q ha hb
    | true =>
      simp only [d13844, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29596 q ha hb
  have h9 (q : Pattern) (ha : d13845 q = 1) (hb : d146836 q = 1) : d152528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13845, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13846 q = 1) (hb : d146836 q = 1) : d152529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13846, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13847 q = 1) (hb : d146836 q = 1) : d152530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13847, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13895 q = 1) (hb : d146836 q = 1) : d152541 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13895, d152541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13895, d152541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13896 q = 1) (hb : d146836 q = 1) : d152542 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13896, d152542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13896, d152542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro29626 (p : Pattern) (ha : d13902 p = 1) (hb : d146836 p = 1) : d152548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d146836 q = 1) : d152543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29625 q ha hb
    | true =>
      simp only [d13897, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d146836 q = 1) : d152544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13899 q = 1) (hb : d146836 q = 1) : d152545 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13899, d152545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13899, d152545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13900 q = 1) (hb : d146836 q = 1) : d152546 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13900, d152546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13900, d152546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13901 q = 1) (hb : d146836 q = 1) : d152547 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13901, d152547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13901, d152547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13902 q = 1) (hb : d146836 q = 1) : d152548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13902, d152548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13902, d152548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29627 (p : Pattern) (ha : d115507 p = 1) (hb : d146836 p = 1) : d152554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13856 q = 1) (hb : d146836 q = 1) : d152539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13856, d152539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29623 q ha hb
    | true =>
      simp only [d13856, d152539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29624 q ha hb
  have h2 (q : Pattern) (ha : d115503 q = 1) (hb : d146836 q = 1) : d152540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d152540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115503, d152540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13903 q = 1) (hb : d146836 q = 1) : d152549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13903, d152549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29626 q ha hb
    | true =>
      simp only [d13903, d152549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13904 q = 1) (hb : d146836 q = 1) : d152550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13904, d152550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13904, d152550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115504 q = 1) (hb : d146836 q = 1) : d152551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d152551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115504, d152551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115505 q = 1) (hb : d146836 q = 1) : d152552 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d152552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115505, d152552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115506 q = 1) (hb : d146836 q = 1) : d152553 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d152553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115506, d152553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115507 q = 1) (hb : d146836 q = 1) : d152554 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d152554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115507, d152554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29628 (p : Pattern) (ha : d115513 p = 1) (hb : d146836 p = 1) : d152571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13641 q = 1) (hb : d146836 q = 1) : d152379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13641, d152379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13641, d152379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29586 q ha hb
  have h2 (q : Pattern) (ha : d13642 q = 1) (hb : d146836 q = 1) : d152380 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13642, d152380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13642, d152380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13651 q = 1) (hb : d146836 q = 1) : d152389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29586 q ha hb
    | true =>
      simp only [d13651, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29589 q ha hb
  have h4 (q : Pattern) (ha : d13652 q = 1) (hb : d146836 q = 1) : d152390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13652, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13653 q = 1) (hb : d146836 q = 1) : d152391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13653, d152391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13653, d152391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115491 q = 1) (hb : d146836 q = 1) : d152467 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d152467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29608 q ha hb
    | true =>
      simp only [d115491, d152467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29616 q ha hb
  have h7 (q : Pattern) (ha : d13794 q = 1) (hb : d146836 q = 1) : d152485 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13794, d152485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29592 q ha hb
    | true =>
      simp only [d13794, d152485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29593 q ha hb
  have h8 (q : Pattern) (ha : d115492 q = 1) (hb : d146836 q = 1) : d152486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d152486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115492, d152486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115493 q = 1) (hb : d146836 q = 1) : d152487 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d152487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115493, d152487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115494 q = 1) (hb : d146836 q = 1) : d152488 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d152488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115494, d152488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115498 q = 1) (hb : d146836 q = 1) : d152492 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d152492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115498, d152492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29617 q ha hb
  have h12 (q : Pattern) (ha : d13803 q = 1) (hb : d146836 q = 1) : d152494 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13803, d152494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13803, d152494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29594 q ha hb
  have h13 (q : Pattern) (ha : d115499 q = 1) (hb : d146836 q = 1) : d152495 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d152495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115499, d152495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115500 q = 1) (hb : d146836 q = 1) : d152496 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d152496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115500, d152496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115501 q = 1) (hb : d146836 q = 1) : d152497 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d152497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115501, d152497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115502 q = 1) (hb : d146836 q = 1) : d152498 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d152498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115502, d152498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115508 q = 1) (hb : d146836 q = 1) : d152555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d152555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115508, d152555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29627 q ha hb
  have h18 (q : Pattern) (ha : d13920 q = 1) (hb : d146836 q = 1) : d152566 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13920, d152566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13920, d152566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29599 q ha hb
  have h19 (q : Pattern) (ha : d115509 q = 1) (hb : d146836 q = 1) : d152567 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d152567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115509, d152567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115510 q = 1) (hb : d146836 q = 1) : d152568 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d152568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115510, d152568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115511 q = 1) (hb : d146836 q = 1) : d152569 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d152569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115511, d152569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115512 q = 1) (hb : d146836 q = 1) : d152570 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d152570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115512, d152570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115513 q = 1) (hb : d146836 q = 1) : d152571 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d152571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115513, d152571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29629 (p : Pattern) (ha : d115519 p = 1) (hb : d146836 p = 1) : d152577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115514 q = 1) (hb : d146836 q = 1) : d152572 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d152572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115514, d152572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29628 q ha hb
  have h2 (q : Pattern) (ha : d115515 q = 1) (hb : d146836 q = 1) : d152573 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d152573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115515, d152573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115516 q = 1) (hb : d146836 q = 1) : d152574 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d152574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115516, d152574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115517 q = 1) (hb : d146836 q = 1) : d152575 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d152575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115517, d152575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115518 q = 1) (hb : d146836 q = 1) : d152576 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d152576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115518, d152576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115519 q = 1) (hb : d146836 q = 1) : d152577 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d152577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115519, d152577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29630 (p : Pattern) (ha : d115525 p = 1) (hb : d146836 p = 1) : d152583 p = 1 := by
  have h0 (q : Pattern) (ha : d115354 q = 1) (hb : d146836 q = 1) : d151664 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d151664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29376 q ha hb
    | true =>
      simp only [d115354, d151664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29419 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115394 q = 1) (hb : d146836 q = 1) : d151866 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d151866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115394, d151866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29464 q ha hb
  have h3 (q : Pattern) (ha : d115395 q = 1) (hb : d146836 q = 1) : d151867 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d151867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d151867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115435 q = 1) (hb : d146836 q = 1) : d152103 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d152103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115435, d152103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29520 q ha hb
  have h5 (q : Pattern) (ha : d115436 q = 1) (hb : d146836 q = 1) : d152104 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d152104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115436, d152104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115437 q = 1) (hb : d146836 q = 1) : d152105 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d152105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d152105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115477 q = 1) (hb : d146836 q = 1) : d152341 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d152341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115477, d152341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29576 q ha hb
  have h8 (q : Pattern) (ha : d115478 q = 1) (hb : d146836 q = 1) : d152342 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d152342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115478, d152342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115479 q = 1) (hb : d146836 q = 1) : d152343 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d152343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115479, d152343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115480 q = 1) (hb : d146836 q = 1) : d152344 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d152344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d152344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115520 q = 1) (hb : d146836 q = 1) : d152578 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d152578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115520, d152578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29629 q ha hb
  have h12 (q : Pattern) (ha : d115521 q = 1) (hb : d146836 q = 1) : d152579 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d152579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115521, d152579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115522 q = 1) (hb : d146836 q = 1) : d152580 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d152580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115522, d152580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115523 q = 1) (hb : d146836 q = 1) : d152581 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d152581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115523, d152581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115524 q = 1) (hb : d146836 q = 1) : d152582 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d152582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d152582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115525 q = 1) (hb : d146836 q = 1) : d152583 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d152583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d152583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro29631 (p : Pattern) (ha : d115531 p = 1) (hb : d146836 p = 1) : d152589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115526 q = 1) (hb : d146836 q = 1) : d152584 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d152584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29630 q ha hb
    | true =>
      simp only [d115526, d152584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115527 q = 1) (hb : d146836 q = 1) : d152585 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d152585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d152585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115528 q = 1) (hb : d146836 q = 1) : d152586 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d152586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d152586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115529 q = 1) (hb : d146836 q = 1) : d152587 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d152587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d152587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115530 q = 1) (hb : d146836 q = 1) : d152588 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d152588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d152588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115531 q = 1) (hb : d146836 q = 1) : d152589 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d152589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d152589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29632 (p : Pattern) (ha : d115537 p = 1) (hb : d146836 p = 1) : d152595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115532 q = 1) (hb : d146836 q = 1) : d152590 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d152590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29631 q ha hb
    | true =>
      simp only [d115532, d152590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115533 q = 1) (hb : d146836 q = 1) : d152591 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d152591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d152591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115534 q = 1) (hb : d146836 q = 1) : d152592 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d152592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d152592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115535 q = 1) (hb : d146836 q = 1) : d152593 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d152593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d152593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115536 q = 1) (hb : d146836 q = 1) : d152594 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d152594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d152594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115537 q = 1) (hb : d146836 q = 1) : d152595 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d152595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d152595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29633 (p : Pattern) (ha : d115543 p = 1) (hb : d146836 p = 1) : d152601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115538 q = 1) (hb : d146836 q = 1) : d152596 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d152596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29632 q ha hb
    | true =>
      simp only [d115538, d152596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115539 q = 1) (hb : d146836 q = 1) : d152597 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d152597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d152597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115540 q = 1) (hb : d146836 q = 1) : d152598 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d152598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d152598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115541 q = 1) (hb : d146836 q = 1) : d152599 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d152599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d152599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115542 q = 1) (hb : d146836 q = 1) : d152600 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d152600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d152600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115543 q = 1) (hb : d146836 q = 1) : d152601 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d152601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d152601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29634 (p : Pattern) (ha : d115549 p = 1) (hb : d146836 p = 1) : d152607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115544 q = 1) (hb : d146836 q = 1) : d152602 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d152602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29633 q ha hb
    | true =>
      simp only [d115544, d152602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115545 q = 1) (hb : d146836 q = 1) : d152603 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d152603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d152603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115546 q = 1) (hb : d146836 q = 1) : d152604 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d152604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d152604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115547 q = 1) (hb : d146836 q = 1) : d152605 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d152605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115547, d152605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115548 q = 1) (hb : d146836 q = 1) : d152606 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d152606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115548, d152606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115549 q = 1) (hb : d146836 q = 1) : d152607 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d152607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115549, d152607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29635 (p : Pattern) (ha : d115555 p = 1) (hb : d146836 p = 1) : d152613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115550 q = 1) (hb : d146836 q = 1) : d152608 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d152608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29634 q ha hb
    | true =>
      simp only [d115550, d152608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115551 q = 1) (hb : d146836 q = 1) : d152609 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d152609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d152609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115552 q = 1) (hb : d146836 q = 1) : d152610 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d115552, d152610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115552, d152610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115553 q = 1) (hb : d146836 q = 1) : d152611 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d152611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115553, d152611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115554 q = 1) (hb : d146836 q = 1) : d152612 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d152612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115554, d152612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115555 q = 1) (hb : d146836 q = 1) : d152613 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d152613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115555, d152613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29636 (p : Pattern) (ha : d115561 p = 1) (hb : d146836 p = 1) : d152619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115556 q = 1) (hb : d146836 q = 1) : d152614 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d152614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29635 q ha hb
    | true =>
      simp only [d115556, d152614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115557 q = 1) (hb : d146836 q = 1) : d152615 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d152615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d152615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115558 q = 1) (hb : d146836 q = 1) : d152616 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d152616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d152616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115559 q = 1) (hb : d146836 q = 1) : d152617 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d152617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d152617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115560 q = 1) (hb : d146836 q = 1) : d152618 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d152618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d152618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115561 q = 1) (hb : d146836 q = 1) : d152619 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d152619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d152619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29637 (p : Pattern) (ha : d115567 p = 1) (hb : d146836 p = 1) : d152625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115562 q = 1) (hb : d146836 q = 1) : d152620 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d152620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29636 q ha hb
    | true =>
      simp only [d115562, d152620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115563 q = 1) (hb : d146836 q = 1) : d152621 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d152621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d152621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115564 q = 1) (hb : d146836 q = 1) : d152622 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d152622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d152622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115565 q = 1) (hb : d146836 q = 1) : d152623 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d152623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d152623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115566 q = 1) (hb : d146836 q = 1) : d152624 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d152624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d152624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115567 q = 1) (hb : d146836 q = 1) : d152625 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d152625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d152625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29638 (p : Pattern) (ha : d146845 p = 1) (hb : d151290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146840 q = 1) (hb : d151285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146840, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28070 q ha hb
    | true =>
      simp only [d146840, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h2 (q : Pattern) (ha : d146841 q = 1) (hb : d151286 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146841, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146841, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146842 q = 1) (hb : d151287 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146842, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146842, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d146843 q = 1) (hb : d151288 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146843, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146843, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d146844 q = 1) (hb : d151289 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d146844, d151289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146844, d151289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146845 q = 1) (hb : d151290 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d146845, d151290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146845, d151290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29639 (p : Pattern) (ha : d146851 p = 1) (hb : d151296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d151291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29638 q ha hb
    | true =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d151292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d151293 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146849 q = 1) (hb : d151294 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146849, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146849, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146850 q = 1) (hb : d151295 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146850, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146850, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146851 q = 1) (hb : d151296 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146851, d151296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146851, d151296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29640 (p : Pattern) (ha : d146857 p = 1) (hb : d151302 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d146852 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29639 q ha hb
    | true =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d146853 q = 1) (hb : d151298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146853, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146853, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d146854 q = 1) (hb : d151299 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146854, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146854, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146855 q = 1) (hb : d151300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146855, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d146855, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146856 q = 1) (hb : d151301 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146856, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146856, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146857 q = 1) (hb : d151302 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146857, d151302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146857, d151302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro29641 (p : Pattern) (ha : d146858 p = 1) (hb : d151303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d151291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29638 q ha hb
    | true =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d151292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d151293 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146849 q = 1) (hb : d151294 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146849, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146849, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146850 q = 1) (hb : d151295 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146850, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146850, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146858 q = 1) (hb : d151303 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146858, d151303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146858, d151303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29642 (p : Pattern) (ha : d146864 p = 1) (hb : d151309 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d146852 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29639 q ha hb
    | true =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d146853 q = 1) (hb : d151298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146853, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146853, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d146854 q = 1) (hb : d151299 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146854, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146854, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146855 q = 1) (hb : d151300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146855, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d146855, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146856 q = 1) (hb : d151301 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146856, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146856, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d146859 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29641 q ha hb
    | true =>
      simp only [d146859, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d146860 q = 1) (hb : d151305 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146860, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d146860, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d146861 q = 1) (hb : d151306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146861, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d146861, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d146862 q = 1) (hb : d151307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146862, d151307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d146862, d151307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d146863 q = 1) (hb : d151308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146863, d151308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d146863, d151308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d146864 q = 1) (hb : d151309 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146864, d151309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146864, d151309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro29643 (p : Pattern) (ha : d146871 p = 1) (hb : d151316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146859 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29641 q ha hb
    | true =>
      simp only [d146859, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146860 q = 1) (hb : d151305 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146860, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146860, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d146861 q = 1) (hb : d151306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146861, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146861, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d146869 q = 1) (hb : d151314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146869, d151314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146869, d151314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146870 q = 1) (hb : d151315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146870, d151315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146870, d151315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146871 q = 1) (hb : d151316 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146871, d151316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146871, d151316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29644 (p : Pattern) (ha : d146884 p = 1) (hb : d151327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146879 q = 1) (hb : d151322 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146879, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28077 q ha hb
    | true =>
      simp only [d146879, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h2 (q : Pattern) (ha : d146880 q = 1) (hb : d151323 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146880, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146880, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146881 q = 1) (hb : d151324 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146881, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146881, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d146882 q = 1) (hb : d151325 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146882, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146882, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d146883 q = 1) (hb : d151326 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d146883, d151326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146883, d151326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146884 q = 1) (hb : d151327 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d146884, d151327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146884, d151327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29645 (p : Pattern) (ha : d146890 p = 1) (hb : d151333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146885 q = 1) (hb : d151328 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146885, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29644 q ha hb
    | true =>
      simp only [d146885, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146886 q = 1) (hb : d151329 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146886, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146886, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146887 q = 1) (hb : d151330 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146887, d151330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146887, d151330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146888 q = 1) (hb : d151331 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146888, d151331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146888, d151331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146889 q = 1) (hb : d151332 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146889, d151332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146889, d151332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146890 q = 1) (hb : d151333 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146890, d151333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146890, d151333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29646 (p : Pattern) (ha : d146896 p = 1) (hb : d151339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146891 q = 1) (hb : d151334 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146891, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29645 q ha hb
    | true =>
      simp only [d146891, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146892 q = 1) (hb : d151335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146892, d151335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146892, d151335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d146893 q = 1) (hb : d151336 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146893, d151336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146893, d151336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d146894 q = 1) (hb : d151337 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146894, d151337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146894, d151337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146895 q = 1) (hb : d151338 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146895, d151338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146895, d151338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146896 q = 1) (hb : d151339 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146896, d151339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146896, d151339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29647 (p : Pattern) (ha : d146902 p = 1) (hb : d151345 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d146865 q = 1) (hb : d151310 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146865, d151310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29640 q ha hb
    | true =>
      simp only [d146865, d151310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29642 q ha hb
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
  have h8 (q : Pattern) (ha : d146866 q = 1) (hb : d151311 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146866, d151311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146866, d151311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146867 q = 1) (hb : d151312 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146867, d151312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146867, d151312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146868 q = 1) (hb : d151313 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146868, d151313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d146868, d151313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146872 q = 1) (hb : d151317 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146872, d151317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146872, d151317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29643 q ha hb
  have h12 (q : Pattern) (ha : d146873 q = 1) (hb : d151318 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146873, d151318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d146873, d151318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146874 q = 1) (hb : d151319 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146874, d151319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d146874, d151319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146875 q = 1) (hb : d151320 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146875, d151320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146875, d151320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146876 q = 1) (hb : d151321 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146876, d151321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146876, d151321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146897 q = 1) (hb : d151340 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146897, d151340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146897, d151340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29646 q ha hb
  have h17 (q : Pattern) (ha : d146898 q = 1) (hb : d151341 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146898, d151341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d146898, d151341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d146899 q = 1) (hb : d151342 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146899, d151342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d146899, d151342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d146900 q = 1) (hb : d151343 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146900, d151343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d146900, d151343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d146901 q = 1) (hb : d151344 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146901, d151344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d146901, d151344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146902 q = 1) (hb : d151345 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d146902, d151345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146902, d151345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro29648 (p : Pattern) (ha : d146912 p = 1) (hb : d151355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146852 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29639 q ha hb
    | true =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d146908 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146908, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146908, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146909 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146909, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146909, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146910 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146910, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146910, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146911 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146911, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146911, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146912 q = 1) (hb : d151355 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146912, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146912, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29649 (p : Pattern) (ha : d146919 p = 1) (hb : d151362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146852 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29639 q ha hb
    | true =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d146908 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146908, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146908, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146909 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146909, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146909, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146910 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146910, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146910, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146911 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146911, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146911, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146859 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29641 q ha hb
    | true =>
      simp only [d146859, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d146915 q = 1) (hb : d151358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146915, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146915, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146916 q = 1) (hb : d151359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146916, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146916, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146917 q = 1) (hb : d151360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146917, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146917, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146918 q = 1) (hb : d151361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146918, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146918, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146919 q = 1) (hb : d151362 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146919, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146919, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29650 (p : Pattern) (ha : d146924 p = 1) (hb : d151367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d151291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29638 q ha hb
    | true =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d151292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d151293 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146849 q = 1) (hb : d151294 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146849, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146849, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146923 q = 1) (hb : d151366 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146923, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146923, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146924 q = 1) (hb : d151367 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146924, d151367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146924, d151367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29651 (p : Pattern) (ha : d146931 p = 1) (hb : d151374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d151291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29638 q ha hb
    | true =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d151292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d151293 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146929 q = 1) (hb : d151372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146929, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146929, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146930 q = 1) (hb : d151373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146930, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146930, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146931 q = 1) (hb : d151374 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146931, d151374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146931, d151374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29652 (p : Pattern) (ha : d146948 p = 1) (hb : d151383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146943 q = 1) (hb : d151378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146943, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28087 q ha hb
    | true =>
      simp only [d146943, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28070 q ha hb
  have h2 (q : Pattern) (ha : d146944 q = 1) (hb : d151379 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146944, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146944, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146945 q = 1) (hb : d151380 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146945, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146945, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146840 q = 1) (hb : d151285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146840, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28070 q ha hb
    | true =>
      simp only [d146840, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h5 (q : Pattern) (ha : d146841 q = 1) (hb : d151286 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146841, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146841, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146842 q = 1) (hb : d151287 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146842, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146842, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146946 q = 1) (hb : d151381 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146946, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146946, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d146843 q = 1) (hb : d151288 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146843, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146843, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d146947 q = 1) (hb : d151382 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d146947, d151382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146947, d151382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146948 q = 1) (hb : d151383 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d146948, d151383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d146948, d151383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29653 (p : Pattern) (ha : d146954 p = 1) (hb : d151389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146949 q = 1) (hb : d151384 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146949, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29652 q ha hb
    | true =>
      simp only [d146949, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146950 q = 1) (hb : d151385 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146950, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146950, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146846 q = 1) (hb : d151291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29638 q ha hb
    | true =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146847 q = 1) (hb : d151292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146951 q = 1) (hb : d151386 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146951, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146951, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146952 q = 1) (hb : d151387 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146952, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146952, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146953 q = 1) (hb : d151388 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146953, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146953, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146954 q = 1) (hb : d151389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146954, d151389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146954, d151389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29654 (p : Pattern) (ha : d146960 p = 1) (hb : d151395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d151291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29638 q ha hb
    | true =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d151292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146957 q = 1) (hb : d151392 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146957, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146957, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146958 q = 1) (hb : d151393 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146958, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146958, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146959 q = 1) (hb : d151394 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146959, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146959, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146960 q = 1) (hb : d151395 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146960, d151395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146960, d151395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29655 (p : Pattern) (ha : d146966 p = 1) (hb : d151401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146925 q = 1) (hb : d151368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146925, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29650 q ha hb
    | true =>
      simp only [d146925, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d146926 q = 1) (hb : d151369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146926, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146926, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146927 q = 1) (hb : d151370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146927, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146927, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146928 q = 1) (hb : d151371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146928, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146928, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146932 q = 1) (hb : d151375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146932, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29651 q ha hb
    | true =>
      simp only [d146932, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d146933 q = 1) (hb : d151376 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146933, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146933, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146934 q = 1) (hb : d151377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146934, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146934, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146955 q = 1) (hb : d151390 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146955, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29653 q ha hb
    | true =>
      simp only [d146955, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29639 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d146852 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d146956 q = 1) (hb : d151391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146956, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d146961 q = 1) (hb : d151396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146961, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29654 q ha hb
    | true =>
      simp only [d146961, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146962 q = 1) (hb : d151397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146962, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d146962, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146963 q = 1) (hb : d151398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146963, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146964 q = 1) (hb : d151399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146964, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146965 q = 1) (hb : d151400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146965, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146966 q = 1) (hb : d151401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146966, d151401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146966, d151401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro29656 (p : Pattern) (ha : d146967 p = 1) (hb : d151402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d151291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29638 q ha hb
    | true =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d151292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d151293 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146849 q = 1) (hb : d151294 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146849, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146849, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146923 q = 1) (hb : d151366 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146923, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146923, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146967 q = 1) (hb : d151402 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146967, d151402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146967, d151402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29657 (p : Pattern) (ha : d146972 p = 1) (hb : d151407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d151291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29638 q ha hb
    | true =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d151292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d151293 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146929 q = 1) (hb : d151372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146929, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146929, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146930 q = 1) (hb : d151373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146930, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146930, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146972 q = 1) (hb : d151407 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146972, d151407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146972, d151407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29658 (p : Pattern) (ha : d146976 p = 1) (hb : d151411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146949 q = 1) (hb : d151384 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146949, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29652 q ha hb
    | true =>
      simp only [d146949, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146950 q = 1) (hb : d151385 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146950, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146950, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146846 q = 1) (hb : d151291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29638 q ha hb
    | true =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146847 q = 1) (hb : d151292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146951 q = 1) (hb : d151386 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146951, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146951, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146952 q = 1) (hb : d151387 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146952, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146952, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146953 q = 1) (hb : d151388 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146953, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146953, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146976 q = 1) (hb : d151411 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146976, d151411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146976, d151411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29659 (p : Pattern) (ha : d146979 p = 1) (hb : d151414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d151291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29638 q ha hb
    | true =>
      simp only [d146846, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d151292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146957 q = 1) (hb : d151392 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146957, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146957, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146958 q = 1) (hb : d151393 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146958, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146958, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146959 q = 1) (hb : d151394 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146959, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146959, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146979 q = 1) (hb : d151414 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146979, d151414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146979, d151414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29660 (p : Pattern) (ha : d146985 p = 1) (hb : d151420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146925 q = 1) (hb : d151368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146925, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29650 q ha hb
    | true =>
      simp only [d146925, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d146926 q = 1) (hb : d151369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146926, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146926, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146927 q = 1) (hb : d151370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146927, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146927, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146928 q = 1) (hb : d151371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146928, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146928, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146932 q = 1) (hb : d151375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146932, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29651 q ha hb
    | true =>
      simp only [d146932, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d146933 q = 1) (hb : d151376 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146933, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146933, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146934 q = 1) (hb : d151377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146934, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146934, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146955 q = 1) (hb : d151390 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146955, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29653 q ha hb
    | true =>
      simp only [d146955, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29639 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d146852 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d146956 q = 1) (hb : d151391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146956, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d146961 q = 1) (hb : d151396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146961, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29654 q ha hb
    | true =>
      simp only [d146961, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146962 q = 1) (hb : d151397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146962, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d146962, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146963 q = 1) (hb : d151398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146963, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146964 q = 1) (hb : d151399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146964, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146965 q = 1) (hb : d151400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146965, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146968 q = 1) (hb : d151403 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146968, d151403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29656 q ha hb
    | true =>
      simp only [d146968, d151403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d146969 q = 1) (hb : d151404 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146969, d151404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146969, d151404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146970 q = 1) (hb : d151405 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146970, d151405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d146970, d151405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d146971 q = 1) (hb : d151406 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146971, d151406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146971, d151406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d146973 q = 1) (hb : d151408 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146973, d151408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29657 q ha hb
    | true =>
      simp only [d146973, d151408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d146974 q = 1) (hb : d151409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146974, d151409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146974, d151409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d146975 q = 1) (hb : d151410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146975, d151410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d146975, d151410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146977 q = 1) (hb : d151412 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146977, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29658 q ha hb
    | true =>
      simp only [d146977, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29641 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d146859 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d146978 q = 1) (hb : d151413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d146978, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d146980 q = 1) (hb : d151415 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146980, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29659 q ha hb
    | true =>
      simp only [d146980, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d146981 q = 1) (hb : d151416 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146981, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d146981, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d146982 q = 1) (hb : d151417 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d146982, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146983 q = 1) (hb : d151418 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146983, d151418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d146983, d151418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d146984 q = 1) (hb : d151419 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146984, d151419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d146984, d151419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d146985 q = 1) (hb : d151420 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146985, d151420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146985, d151420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro29661 (p : Pattern) (ha : d146987 p = 1) (hb : d151422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146852 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29639 q ha hb
    | true =>
      simp only [d146852, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d146908 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146908, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146908, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146909 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146909, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146909, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146910 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146910, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146910, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146911 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146911, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146911, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d146987 q = 1) (hb : d151422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146987, d151422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146987, d151422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro29662 (p : Pattern) (ha : d146994 p = 1) (hb : d151429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146977 q = 1) (hb : d151412 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146977, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29658 q ha hb
    | true =>
      simp only [d146977, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29641 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146859 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146978 q = 1) (hb : d151413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146978, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d146980 q = 1) (hb : d151415 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146980, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29659 q ha hb
    | true =>
      simp only [d146980, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146981 q = 1) (hb : d151416 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146981, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146981, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146982 q = 1) (hb : d151417 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146982, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146992 q = 1) (hb : d151427 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146992, d151427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146992, d151427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146993 q = 1) (hb : d151428 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146993, d151428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146993, d151428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146994 q = 1) (hb : d151429 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146994, d151429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146994, d151429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29663 (p : Pattern) (ha : d147012 p = 1) (hb : d151440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147007 q = 1) (hb : d151435 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147007, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28099 q ha hb
    | true =>
      simp only [d147007, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28077 q ha hb
  have h2 (q : Pattern) (ha : d147008 q = 1) (hb : d151436 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147008, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147008, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147009 q = 1) (hb : d151437 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147009, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147009, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146879 q = 1) (hb : d151322 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146879, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28077 q ha hb
    | true =>
      simp only [d146879, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h5 (q : Pattern) (ha : d146880 q = 1) (hb : d151323 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146880, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146880, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146881 q = 1) (hb : d151324 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146881, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146881, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147010 q = 1) (hb : d151438 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147010, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147010, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d146882 q = 1) (hb : d151325 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146882, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146882, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d147011 q = 1) (hb : d151439 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147011, d151439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147011, d151439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147012 q = 1) (hb : d151440 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147012, d151440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147012, d151440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro29664 (p : Pattern) (ha : d147018 p = 1) (hb : d151446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147013 q = 1) (hb : d151441 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147013, d151441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29663 q ha hb
    | true =>
      simp only [d147013, d151441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147014 q = 1) (hb : d151442 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147014, d151442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147014, d151442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146885 q = 1) (hb : d151328 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146885, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29644 q ha hb
    | true =>
      simp only [d146885, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146886 q = 1) (hb : d151329 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146886, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146886, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147015 q = 1) (hb : d151443 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147015, d151443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147015, d151443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147016 q = 1) (hb : d151444 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147016, d151444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147016, d151444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147017 q = 1) (hb : d151445 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147017, d151445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147017, d151445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147018 q = 1) (hb : d151446 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147018, d151446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147018, d151446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29665 (p : Pattern) (ha : d147024 p = 1) (hb : d151452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146885 q = 1) (hb : d151328 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146885, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29644 q ha hb
    | true =>
      simp only [d146885, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146886 q = 1) (hb : d151329 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146886, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146886, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147021 q = 1) (hb : d151449 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147021, d151449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147021, d151449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147022 q = 1) (hb : d151450 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147022, d151450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147022, d151450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147023 q = 1) (hb : d151451 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147023, d151451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147023, d151451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147024 q = 1) (hb : d151452 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147024, d151452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147024, d151452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29666 (p : Pattern) (ha : d147030 p = 1) (hb : d151458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147019 q = 1) (hb : d151447 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147019, d151447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29664 q ha hb
    | true =>
      simp only [d147019, d151447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29645 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146891 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147020 q = 1) (hb : d151448 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147020, d151448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147020, d151448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147025 q = 1) (hb : d151453 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147025, d151453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29665 q ha hb
    | true =>
      simp only [d147025, d151453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147026 q = 1) (hb : d151454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147026, d151454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147026, d151454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147027 q = 1) (hb : d151455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147027, d151455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147027, d151455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147028 q = 1) (hb : d151456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147028, d151456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147028, d151456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147029 q = 1) (hb : d151457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147029, d151457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147029, d151457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147030 q = 1) (hb : d151458 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147030, d151458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147030, d151458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29667 (p : Pattern) (ha : d147036 p = 1) (hb : d151464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146913 q = 1) (hb : d151356 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146913, d151356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146913, d151356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29648 q ha hb
  have h2 (q : Pattern) (ha : d146914 q = 1) (hb : d151357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146914, d151357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146914, d151357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146920 q = 1) (hb : d151363 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146920, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29648 q ha hb
    | true =>
      simp only [d146920, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29649 q ha hb
  have h4 (q : Pattern) (ha : d146921 q = 1) (hb : d151364 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146921, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146921, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146922 q = 1) (hb : d151365 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146922, d151365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146922, d151365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146986 q = 1) (hb : d151421 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146986, d151421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29655 q ha hb
    | true =>
      simp only [d146986, d151421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29660 q ha hb
  have h7 (q : Pattern) (ha : d146988 q = 1) (hb : d151423 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146988, d151423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29661 q ha hb
    | true =>
      simp only [d146988, d151423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d146989 q = 1) (hb : d151424 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146989, d151424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146989, d151424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146990 q = 1) (hb : d151425 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146990, d151425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146990, d151425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146991 q = 1) (hb : d151426 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146991, d151426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146991, d151426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146995 q = 1) (hb : d151430 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146995, d151430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146995, d151430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29662 q ha hb
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
  have h13 (q : Pattern) (ha : d146996 q = 1) (hb : d151431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146996, d151431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d146996, d151431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146997 q = 1) (hb : d151432 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146997, d151432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146997, d151432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146998 q = 1) (hb : d151433 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146998, d151433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d146998, d151433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146999 q = 1) (hb : d151434 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146999, d151434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146999, d151434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147031 q = 1) (hb : d151459 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147031, d151459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147031, d151459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29666 q ha hb
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
  have h19 (q : Pattern) (ha : d147032 q = 1) (hb : d151460 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147032, d151460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147032, d151460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d147033 q = 1) (hb : d151461 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147033, d151461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147033, d151461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d147034 q = 1) (hb : d151462 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147034, d151462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d147034, d151462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d147035 q = 1) (hb : d151463 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147035, d151463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147035, d151463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147036 q = 1) (hb : d151464 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147036, d151464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147036, d151464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29668 (p : Pattern) (ha : d147042 p = 1) (hb : d151470 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d146903 q = 1) (hb : d151346 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d146903, d151346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146903, d151346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29647 q ha hb
  have h6 (q : Pattern) (ha : d146904 q = 1) (hb : d151347 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d146904, d151347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146904, d151347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146905 q = 1) (hb : d151348 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d146905, d151348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146905, d151348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146906 q = 1) (hb : d151349 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d146906, d151349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146906, d151349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146907 q = 1) (hb : d151350 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d146907, d151350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146907, d151350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147037 q = 1) (hb : d151465 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147037, d151465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147037, d151465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29667 q ha hb
  have h11 (q : Pattern) (ha : d147038 q = 1) (hb : d151466 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147038, d151466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147038, d151466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d147039 q = 1) (hb : d151467 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147039, d151467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147039, d151467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147040 q = 1) (hb : d151468 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147040, d151468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147040, d151468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147041 q = 1) (hb : d151469 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147041, d151469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147041, d151469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147042 q = 1) (hb : d151470 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147042, d151470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147042, d151470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29669 (p : Pattern) (ha : d147045 p = 1) (hb : d151473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146943 q = 1) (hb : d151378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146943, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28087 q ha hb
    | true =>
      simp only [d146943, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28070 q ha hb
  have h2 (q : Pattern) (ha : d146944 q = 1) (hb : d151379 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146944, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146944, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146945 q = 1) (hb : d151380 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146945, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146945, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146840 q = 1) (hb : d151285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146840, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28070 q ha hb
    | true =>
      simp only [d146840, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h5 (q : Pattern) (ha : d146841 q = 1) (hb : d151286 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146841, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146841, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146842 q = 1) (hb : d151287 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146842, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146842, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146946 q = 1) (hb : d151381 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146946, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146946, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147043 q = 1) (hb : d151471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147043, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147043, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147044 q = 1) (hb : d151472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147044, d151472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147044, d151472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147045 q = 1) (hb : d151473 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147045, d151473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147045, d151473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29670 (p : Pattern) (ha : d147049 p = 1) (hb : d151477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146840 q = 1) (hb : d151285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146840, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28070 q ha hb
    | true =>
      simp only [d146840, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h2 (q : Pattern) (ha : d146841 q = 1) (hb : d151286 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146841, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146841, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146842 q = 1) (hb : d151287 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146842, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146842, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147043 q = 1) (hb : d151471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147043, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147043, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147048 q = 1) (hb : d151476 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147048, d151476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147048, d151476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147049 q = 1) (hb : d151477 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147049, d151477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147049, d151477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29671 (p : Pattern) (ha : d147055 p = 1) (hb : d151483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d151474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29669 q ha hb
    | true =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d151475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d151480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147053 q = 1) (hb : d151481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147053, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147053, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147054 q = 1) (hb : d151482 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147054, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147054, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147055 q = 1) (hb : d151483 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147055, d151483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147055, d151483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29672 (p : Pattern) (ha : d147059 p = 1) (hb : d151487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d151484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147057 q = 1) (hb : d151485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147057, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147057, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147058 q = 1) (hb : d151486 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147058, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147058, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147059 q = 1) (hb : d151487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147059, d151487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147059, d151487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29673 (p : Pattern) (ha : d147065 p = 1) (hb : d151493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147060 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29671 q ha hb
    | true =>
      simp only [d147060, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29672 q ha hb
  have h2 (q : Pattern) (ha : d147061 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147061, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147061, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147062 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147062, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147062, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147063 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147063, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147063, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147064 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147064, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147064, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147065 q = 1) (hb : d151493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147065, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147065, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29674 (p : Pattern) (ha : d147068 p = 1) (hb : d151496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d151474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29669 q ha hb
    | true =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d151475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d151480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147053 q = 1) (hb : d151481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147053, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147053, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147054 q = 1) (hb : d151482 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147054, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147054, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147068 q = 1) (hb : d151496 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147068, d151496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147068, d151496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29675 (p : Pattern) (ha : d147069 p = 1) (hb : d151497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d151484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147057 q = 1) (hb : d151485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147057, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147057, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147058 q = 1) (hb : d151486 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147058, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147058, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147069 q = 1) (hb : d151497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147069, d151497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147069, d151497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29676 (p : Pattern) (ha : d147075 p = 1) (hb : d151503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147060 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29671 q ha hb
    | true =>
      simp only [d147060, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29672 q ha hb
  have h2 (q : Pattern) (ha : d147061 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147061, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147061, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147062 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147062, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147062, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147063 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147063, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147063, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147064 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147064, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147064, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147070 q = 1) (hb : d151498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29674 q ha hb
    | true =>
      simp only [d147070, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29675 q ha hb
  have h7 (q : Pattern) (ha : d147071 q = 1) (hb : d151499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147071, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147071, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147072 q = 1) (hb : d151500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147072, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147072, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147073 q = 1) (hb : d151501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147073, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147073, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147074 q = 1) (hb : d151502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147074, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147074, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147075 q = 1) (hb : d151503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147075, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147075, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29677 (p : Pattern) (ha : d147080 p = 1) (hb : d151508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d151474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29669 q ha hb
    | true =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d151475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d151480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147053 q = 1) (hb : d151481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147053, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147053, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147079 q = 1) (hb : d151507 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147079, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147079, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147080 q = 1) (hb : d151508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147080, d151508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147080, d151508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29678 (p : Pattern) (ha : d147082 p = 1) (hb : d151510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d151484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147057 q = 1) (hb : d151485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147057, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147057, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147081 q = 1) (hb : d151509 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147081, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147081, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147082 q = 1) (hb : d151510 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147082, d151510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147082, d151510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29679 (p : Pattern) (ha : d147089 p = 1) (hb : d151517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d151474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29669 q ha hb
    | true =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d151475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d151480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147087 q = 1) (hb : d151515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147087, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147087, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147088 q = 1) (hb : d151516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147088, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147088, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147089 q = 1) (hb : d151517 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147089, d151517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147089, d151517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29680 (p : Pattern) (ha : d147092 p = 1) (hb : d151520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d151484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147090 q = 1) (hb : d151518 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147090, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147090, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147091 q = 1) (hb : d151519 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147091, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147091, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147092 q = 1) (hb : d151520 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147092, d151520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147092, d151520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29681 (p : Pattern) (ha : d147112 p = 1) (hb : d151527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5451 q = 1) (hb : d74177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9259 q ha hb
    | true =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5452 q = 1) (hb : d74178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5453 q = 1) (hb : d74179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d74179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d74179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5454 q = 1) (hb : d74180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d74180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5454, d74180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20995 q = 1) (hb : d146941 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d146941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20995, d146941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d147112 q = 1) (hb : d151527 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147112, d151527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147112, d151527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro29682 (p : Pattern) (ha : d147118 p = 1) (hb : d151533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147109 q = 1) (hb : d151524 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147109, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28119 q ha hb
    | true =>
      simp only [d147109, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28087 q ha hb
  have h2 (q : Pattern) (ha : d147110 q = 1) (hb : d151525 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147110, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147110, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147111 q = 1) (hb : d151526 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147111, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147111, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147113 q = 1) (hb : d151528 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147113, d151528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28087 q ha hb
    | true =>
      simp only [d147113, d151528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29681 q ha hb
  have h5 (q : Pattern) (ha : d147114 q = 1) (hb : d151529 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147114, d151529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147114, d151529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147115 q = 1) (hb : d151530 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147115, d151530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147115, d151530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147116 q = 1) (hb : d151531 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147116, d151531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147116, d151531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146943 q = 1) (hb : d151378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146943, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28087 q ha hb
    | true =>
      simp only [d146943, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28070 q ha hb
  have h9 (q : Pattern) (ha : d146944 q = 1) (hb : d151379 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146944, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146944, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146945 q = 1) (hb : d151380 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146945, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146945, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146840 q = 1) (hb : d151285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146840, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28070 q ha hb
    | true =>
      simp only [d146840, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h12 (q : Pattern) (ha : d146841 q = 1) (hb : d151286 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146841, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146841, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146842 q = 1) (hb : d151287 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146842, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146842, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146946 q = 1) (hb : d151381 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146946, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146946, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147117 q = 1) (hb : d151532 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147117, d151532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147117, d151532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147118 q = 1) (hb : d151533 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147118, d151533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147118, d151533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro29683 (p : Pattern) (ha : d147124 p = 1) (hb : d151539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147119 q = 1) (hb : d151534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147119, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29682 q ha hb
    | true =>
      simp only [d147119, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147120 q = 1) (hb : d151535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147120, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147120, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147046 q = 1) (hb : d151474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29669 q ha hb
    | true =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147047 q = 1) (hb : d151475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147121 q = 1) (hb : d151536 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147121, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147121, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147122 q = 1) (hb : d151537 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147122, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147122, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147123 q = 1) (hb : d151538 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147123, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147123, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147124 q = 1) (hb : d151539 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147124, d151539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147124, d151539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29684 (p : Pattern) (ha : d147130 p = 1) (hb : d151545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d151474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29669 q ha hb
    | true =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d151475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147127 q = 1) (hb : d151542 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147127, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147127, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147128 q = 1) (hb : d151543 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147128, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147128, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147129 q = 1) (hb : d151544 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147129, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147129, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147130 q = 1) (hb : d151545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147130, d151545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147130, d151545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29685 (p : Pattern) (ha : d147136 p = 1) (hb : d151551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147083 q = 1) (hb : d151511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147083, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29677 q ha hb
    | true =>
      simp only [d147083, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29678 q ha hb
  have h2 (q : Pattern) (ha : d147084 q = 1) (hb : d151512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147084, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147084, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147085 q = 1) (hb : d151513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147085, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147085, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147086 q = 1) (hb : d151514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147086, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147086, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147093 q = 1) (hb : d151521 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147093, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29679 q ha hb
    | true =>
      simp only [d147093, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29680 q ha hb
  have h6 (q : Pattern) (ha : d147094 q = 1) (hb : d151522 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147094, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147094, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147095 q = 1) (hb : d151523 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147095, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147095, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147125 q = 1) (hb : d151540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147125, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29683 q ha hb
    | true =>
      simp only [d147125, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29671 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147060 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147126 q = 1) (hb : d151541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147126, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147131 q = 1) (hb : d151546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147131, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29684 q ha hb
    | true =>
      simp only [d147131, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147132 q = 1) (hb : d151547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147132, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147132, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147133 q = 1) (hb : d151548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147133, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147134 q = 1) (hb : d151549 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147134, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147135 q = 1) (hb : d151550 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147135, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147136 q = 1) (hb : d151551 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147136, d151551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147136, d151551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro29686 (p : Pattern) (ha : d147137 p = 1) (hb : d151552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d151474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29669 q ha hb
    | true =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d151475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d151480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147053 q = 1) (hb : d151481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147053, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147053, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147079 q = 1) (hb : d151507 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147079, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147079, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147137 q = 1) (hb : d151552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147137, d151552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147137, d151552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29687 (p : Pattern) (ha : d147138 p = 1) (hb : d151553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d151484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147057 q = 1) (hb : d151485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147057, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147057, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147081 q = 1) (hb : d151509 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147081, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147081, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147138 q = 1) (hb : d151553 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147138, d151553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147138, d151553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29688 (p : Pattern) (ha : d147143 p = 1) (hb : d151558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d151474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29669 q ha hb
    | true =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d151475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d151480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147087 q = 1) (hb : d151515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147087, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147087, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147088 q = 1) (hb : d151516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147088, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147088, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147143 q = 1) (hb : d151558 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147143, d151558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147143, d151558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29689 (p : Pattern) (ha : d147144 p = 1) (hb : d151559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d151478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29670 q ha hb
    | true =>
      simp only [d147050, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d151479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d151484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147090 q = 1) (hb : d151518 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147090, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147090, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147091 q = 1) (hb : d151519 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147091, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147091, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147144 q = 1) (hb : d151559 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147144, d151559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147144, d151559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29690 (p : Pattern) (ha : d147148 p = 1) (hb : d151563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147119 q = 1) (hb : d151534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147119, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29682 q ha hb
    | true =>
      simp only [d147119, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147120 q = 1) (hb : d151535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147120, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147120, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147046 q = 1) (hb : d151474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29669 q ha hb
    | true =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147047 q = 1) (hb : d151475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147121 q = 1) (hb : d151536 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147121, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147121, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147122 q = 1) (hb : d151537 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147122, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147122, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147123 q = 1) (hb : d151538 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147123, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147123, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147148 q = 1) (hb : d151563 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147148, d151563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147148, d151563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29691 (p : Pattern) (ha : d147151 p = 1) (hb : d151566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d151474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29669 q ha hb
    | true =>
      simp only [d147046, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d151475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147127 q = 1) (hb : d151542 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147127, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147127, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147128 q = 1) (hb : d151543 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147128, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147128, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147129 q = 1) (hb : d151544 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147129, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147129, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147151 q = 1) (hb : d151566 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147151, d151566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147151, d151566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29692 (p : Pattern) (ha : d147157 p = 1) (hb : d151572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147083 q = 1) (hb : d151511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147083, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29677 q ha hb
    | true =>
      simp only [d147083, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29678 q ha hb
  have h2 (q : Pattern) (ha : d147084 q = 1) (hb : d151512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147084, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147084, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147085 q = 1) (hb : d151513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147085, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147085, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147086 q = 1) (hb : d151514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147086, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147086, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147093 q = 1) (hb : d151521 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147093, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29679 q ha hb
    | true =>
      simp only [d147093, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29680 q ha hb
  have h6 (q : Pattern) (ha : d147094 q = 1) (hb : d151522 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147094, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147094, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147095 q = 1) (hb : d151523 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147095, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147095, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147125 q = 1) (hb : d151540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147125, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29683 q ha hb
    | true =>
      simp only [d147125, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29671 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147060 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147126 q = 1) (hb : d151541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147126, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147131 q = 1) (hb : d151546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147131, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29684 q ha hb
    | true =>
      simp only [d147131, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147132 q = 1) (hb : d151547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147132, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147132, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147133 q = 1) (hb : d151548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147133, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147134 q = 1) (hb : d151549 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147134, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147135 q = 1) (hb : d151550 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147135, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147139 q = 1) (hb : d151554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147139, d151554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29686 q ha hb
    | true =>
      simp only [d147139, d151554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29687 q ha hb
  have h17 (q : Pattern) (ha : d147140 q = 1) (hb : d151555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147140, d151555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147140, d151555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147141 q = 1) (hb : d151556 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147141, d151556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147141, d151556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d147142 q = 1) (hb : d151557 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147142, d151557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147142, d151557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147145 q = 1) (hb : d151560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147145, d151560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29688 q ha hb
    | true =>
      simp only [d147145, d151560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29689 q ha hb
  have h21 (q : Pattern) (ha : d147146 q = 1) (hb : d151561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147146, d151561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147146, d151561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d147147 q = 1) (hb : d151562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147147, d151562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147147, d151562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147149 q = 1) (hb : d151564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147149, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29690 q ha hb
    | true =>
      simp only [d147149, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29674 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d147070 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d147150 q = 1) (hb : d151565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d147150, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d147152 q = 1) (hb : d151567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147152, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29691 q ha hb
    | true =>
      simp only [d147152, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d147153 q = 1) (hb : d151568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147153, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d147153, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d147154 q = 1) (hb : d151569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d147154, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d147155 q = 1) (hb : d151570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147155, d151570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d147155, d151570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d147156 q = 1) (hb : d151571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147156, d151571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147156, d151571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d147157 q = 1) (hb : d151572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147157, d151572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147157, d151572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro29693 (p : Pattern) (ha : d147164 p = 1) (hb : d151579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147060 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29671 q ha hb
    | true =>
      simp only [d147060, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29672 q ha hb
  have h2 (q : Pattern) (ha : d147061 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147061, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147061, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147062 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147062, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147062, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147063 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147063, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147063, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147064 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147064, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147064, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147159 q = 1) (hb : d151574 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147159, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29672 q ha hb
    | true =>
      simp only [d147159, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147160 q = 1) (hb : d151575 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147160, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147160, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147161 q = 1) (hb : d151576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147161, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147161, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147162 q = 1) (hb : d151577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147162, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147162, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147163 q = 1) (hb : d151578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147163, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147163, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147164 q = 1) (hb : d151579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147164, d151579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147164, d151579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29694 (p : Pattern) (ha : d147170 p = 1) (hb : d151585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147159 q = 1) (hb : d151574 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147159, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29672 q ha hb
    | true =>
      simp only [d147159, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147160 q = 1) (hb : d151575 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147160, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147160, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147161 q = 1) (hb : d151576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147161, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147161, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147162 q = 1) (hb : d151577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147162, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147162, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147163 q = 1) (hb : d151578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147163, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147163, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147165 q = 1) (hb : d151580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147165, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29675 q ha hb
    | true =>
      simp only [d147165, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147166 q = 1) (hb : d151581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147166, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147166, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147167 q = 1) (hb : d151582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147167, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147167, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147168 q = 1) (hb : d151583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147168, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147168, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147169 q = 1) (hb : d151584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147169, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147169, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147170 q = 1) (hb : d151585 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147170, d151585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147170, d151585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29695 (p : Pattern) (ha : d147177 p = 1) (hb : d151592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147149 q = 1) (hb : d151564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147149, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29690 q ha hb
    | true =>
      simp only [d147149, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29674 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147150 q = 1) (hb : d151565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147150, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147152 q = 1) (hb : d151567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147152, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29691 q ha hb
    | true =>
      simp only [d147152, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147153 q = 1) (hb : d151568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147153, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147153, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147154 q = 1) (hb : d151569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147154, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147175 q = 1) (hb : d151590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147175, d151590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147175, d151590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147176 q = 1) (hb : d151591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147176, d151591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147176, d151591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147177 q = 1) (hb : d151592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147177, d151592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147177, d151592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29696 (p : Pattern) (ha : d147179 p = 1) (hb : d151594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147165 q = 1) (hb : d151580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147165, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29675 q ha hb
    | true =>
      simp only [d147165, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147166 q = 1) (hb : d151581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147166, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147166, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147167 q = 1) (hb : d151582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147167, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147167, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147168 q = 1) (hb : d151583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147168, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147168, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147169 q = 1) (hb : d151584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147169, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147169, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147179 q = 1) (hb : d151594 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147179, d151594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147179, d151594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29697 (p : Pattern) (ha : d147199 p = 1) (hb : d151603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5495 q = 1) (hb : d74221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d74221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d74221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9259 q ha hb
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d74177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9259 q ha hb
    | true =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5496 q = 1) (hb : d74222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d74222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5496, d74222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5452 q = 1) (hb : d74178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5497 q = 1) (hb : d74223 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d74223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5497, d74223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5498 q = 1) (hb : d74224 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d74224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5498, d74224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21076 q = 1) (hb : d147005 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d147005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21076, d147005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147199 q = 1) (hb : d151603 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147199, d151603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d147199, d151603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro29698 (p : Pattern) (ha : d147205 p = 1) (hb : d151609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147196 q = 1) (hb : d151600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147196, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28135 q ha hb
    | true =>
      simp only [d147196, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28099 q ha hb
  have h2 (q : Pattern) (ha : d147197 q = 1) (hb : d151601 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147197, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147197, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147198 q = 1) (hb : d151602 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147198, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147198, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147200 q = 1) (hb : d151604 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147200, d151604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28099 q ha hb
    | true =>
      simp only [d147200, d151604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29697 q ha hb
  have h5 (q : Pattern) (ha : d147201 q = 1) (hb : d151605 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147201, d151605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147201, d151605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147202 q = 1) (hb : d151606 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147202, d151606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147202, d151606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147203 q = 1) (hb : d151607 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147203, d151607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147203, d151607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147007 q = 1) (hb : d151435 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147007, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28099 q ha hb
    | true =>
      simp only [d147007, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28077 q ha hb
  have h9 (q : Pattern) (ha : d147008 q = 1) (hb : d151436 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147008, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147008, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147009 q = 1) (hb : d151437 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147009, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147009, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146879 q = 1) (hb : d151322 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146879, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28077 q ha hb
    | true =>
      simp only [d146879, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h12 (q : Pattern) (ha : d146880 q = 1) (hb : d151323 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146880, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146880, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146881 q = 1) (hb : d151324 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146881, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146881, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147010 q = 1) (hb : d151438 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147010, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147010, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147204 q = 1) (hb : d151608 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147204, d151608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147204, d151608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147205 q = 1) (hb : d151609 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147205, d151609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147205, d151609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro29699 (p : Pattern) (ha : d147210 p = 1) (hb : d151614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147007 q = 1) (hb : d151435 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147007, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28099 q ha hb
    | true =>
      simp only [d147007, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28077 q ha hb
  have h2 (q : Pattern) (ha : d147008 q = 1) (hb : d151436 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147008, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147008, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147009 q = 1) (hb : d151437 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147009, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147009, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146879 q = 1) (hb : d151322 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146879, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28077 q ha hb
    | true =>
      simp only [d146879, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h5 (q : Pattern) (ha : d146880 q = 1) (hb : d151323 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146880, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146880, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146881 q = 1) (hb : d151324 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146881, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146881, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147010 q = 1) (hb : d151438 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147010, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147010, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147208 q = 1) (hb : d151612 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147208, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147208, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147209 q = 1) (hb : d151613 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147209, d151613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147209, d151613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147210 q = 1) (hb : d151614 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147210, d151614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147210, d151614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29700 (p : Pattern) (ha : d147216 p = 1) (hb : d151620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147206 q = 1) (hb : d151610 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147206, d151610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29698 q ha hb
    | true =>
      simp only [d147206, d151610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147207 q = 1) (hb : d151611 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147207, d151611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147207, d151611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147211 q = 1) (hb : d151615 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147211, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29699 q ha hb
    | true =>
      simp only [d147211, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147212 q = 1) (hb : d151616 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147212, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147212, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147213 q = 1) (hb : d151617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147213, d151617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147213, d151617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147214 q = 1) (hb : d151618 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147214, d151618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147214, d151618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147215 q = 1) (hb : d151619 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147215, d151619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147215, d151619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147216 q = 1) (hb : d151620 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147216, d151620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147216, d151620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29701 (p : Pattern) (ha : d147218 p = 1) (hb : d151622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146879 q = 1) (hb : d151322 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146879, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28077 q ha hb
    | true =>
      simp only [d146879, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h2 (q : Pattern) (ha : d146880 q = 1) (hb : d151323 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146880, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146880, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146881 q = 1) (hb : d151324 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146881, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146881, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147208 q = 1) (hb : d151612 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147208, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147208, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147217 q = 1) (hb : d151621 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147217, d151621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147217, d151621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147218 q = 1) (hb : d151622 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147218, d151622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147218, d151622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29702 (p : Pattern) (ha : d147224 p = 1) (hb : d151628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147211 q = 1) (hb : d151615 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147211, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29699 q ha hb
    | true =>
      simp only [d147211, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147212 q = 1) (hb : d151616 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147212, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147212, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147219 q = 1) (hb : d151623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147219, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29701 q ha hb
    | true =>
      simp only [d147219, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147220 q = 1) (hb : d151624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147220, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147220, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147221 q = 1) (hb : d151625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147221, d151625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147221, d151625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147222 q = 1) (hb : d151626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147222, d151626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147222, d151626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147223 q = 1) (hb : d151627 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147223, d151627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147223, d151627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147224 q = 1) (hb : d151628 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147224, d151628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147224, d151628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29703 (p : Pattern) (ha : d147235 p = 1) (hb : d151634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147211 q = 1) (hb : d151615 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147211, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29699 q ha hb
    | true =>
      simp only [d147211, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147212 q = 1) (hb : d151616 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147212, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147212, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147232 q = 1) (hb : d151631 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147232, d151631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147232, d151631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147233 q = 1) (hb : d151632 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147233, d151632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147233, d151632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147234 q = 1) (hb : d151633 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147234, d151633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147234, d151633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147235 q = 1) (hb : d151634 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147235, d151634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147235, d151634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29704 (p : Pattern) (ha : d147241 p = 1) (hb : d151640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147225 q = 1) (hb : d151629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147225, d151629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29700 q ha hb
    | true =>
      simp only [d147225, d151629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29702 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147230 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147231 q = 1) (hb : d151630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147231, d151630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147231, d151630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147236 q = 1) (hb : d151635 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147236, d151635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29703 q ha hb
    | true =>
      simp only [d147236, d151635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147237 q = 1) (hb : d151636 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147237, d151636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147237, d151636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147238 q = 1) (hb : d151637 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147238, d151637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147238, d151637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147239 q = 1) (hb : d151638 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147239, d151638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147239, d151638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147240 q = 1) (hb : d151639 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147240, d151639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147240, d151639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147241 q = 1) (hb : d151640 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147241, d151640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147241, d151640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29705 (p : Pattern) (ha : d147229 p = 1) (hb : d151645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147219 q = 1) (hb : d151623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147219, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29701 q ha hb
    | true =>
      simp only [d147219, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147220 q = 1) (hb : d151624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147220, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147220, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147226 q = 1) (hb : d151642 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147226, d151642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147226, d151642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147227 q = 1) (hb : d151643 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147227, d151643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147227, d151643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147228 q = 1) (hb : d151644 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147228, d151644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147228, d151644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147229 q = 1) (hb : d151645 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147229, d151645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147229, d151645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29706 (p : Pattern) (ha : d147248 p = 1) (hb : d151651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147243 q = 1) (hb : d151646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147243, d151646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29705 q ha hb
    | true =>
      simp only [d147243, d151646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147244 q = 1) (hb : d151647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147244, d151647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147244, d151647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147245 q = 1) (hb : d151648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147245, d151648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147245, d151648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147246 q = 1) (hb : d151649 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147246, d151649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147246, d151649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147247 q = 1) (hb : d151650 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147247, d151650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147247, d151650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147248 q = 1) (hb : d151651 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147248, d151651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147248, d151651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29707 (p : Pattern) (ha : d147254 p = 1) (hb : d151657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147066 q = 1) (hb : d151494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147066, d151494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147066, d151494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29673 q ha hb
  have h2 (q : Pattern) (ha : d147067 q = 1) (hb : d151495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147067, d151495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147067, d151495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d147076 q = 1) (hb : d151504 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147076, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29673 q ha hb
    | true =>
      simp only [d147076, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29676 q ha hb
  have h4 (q : Pattern) (ha : d147077 q = 1) (hb : d151505 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147077, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147077, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147078 q = 1) (hb : d151506 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147078, d151506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147078, d151506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147158 q = 1) (hb : d151573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147158, d151573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29685 q ha hb
    | true =>
      simp only [d147158, d151573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29692 q ha hb
  have h7 (q : Pattern) (ha : d147171 q = 1) (hb : d151586 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147171, d151586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29693 q ha hb
    | true =>
      simp only [d147171, d151586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29694 q ha hb
  have h8 (q : Pattern) (ha : d147172 q = 1) (hb : d151587 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147172, d151587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147172, d151587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147173 q = 1) (hb : d151588 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147173, d151588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147173, d151588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d147174 q = 1) (hb : d151589 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147174, d151589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147174, d151589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147178 q = 1) (hb : d151593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147178, d151593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147178, d151593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29695 q ha hb
  have h12 (q : Pattern) (ha : d147180 q = 1) (hb : d151595 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147180, d151595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147180, d151595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29696 q ha hb
  have h13 (q : Pattern) (ha : d147181 q = 1) (hb : d151596 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147181, d151596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147181, d151596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147182 q = 1) (hb : d151597 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147182, d151597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147182, d151597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d147183 q = 1) (hb : d151598 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147183, d151598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d147183, d151598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d147184 q = 1) (hb : d151599 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147184, d151599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147184, d151599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147242 q = 1) (hb : d151641 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147242, d151641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147242, d151641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29704 q ha hb
  have h18 (q : Pattern) (ha : d147249 q = 1) (hb : d151652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147249, d151652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147249, d151652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29706 q ha hb
  have h19 (q : Pattern) (ha : d147250 q = 1) (hb : d151653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147250, d151653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147250, d151653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147251 q = 1) (hb : d151654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147251, d151654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147251, d151654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d147252 q = 1) (hb : d151655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147252, d151655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d147252, d151655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d147253 q = 1) (hb : d151656 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147253, d151656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147253, d151656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147254 q = 1) (hb : d151657 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147254, d151657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147254, d151657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29708 (p : Pattern) (ha : d147260 p = 1) (hb : d151663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147255 q = 1) (hb : d151658 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147255, d151658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147255, d151658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29707 q ha hb
  have h2 (q : Pattern) (ha : d147256 q = 1) (hb : d151659 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147256, d151659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147256, d151659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147257 q = 1) (hb : d151660 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147257, d151660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147257, d151660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147258 q = 1) (hb : d151661 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147258, d151661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147258, d151661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147259 q = 1) (hb : d151662 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147259, d151662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147259, d151662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147260 q = 1) (hb : d151663 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147260, d151663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147260, d151663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29709 (p : Pattern) (ha : d147274 p = 1) (hb : d151671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147265 q = 1) (hb : d151524 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147265, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28147 q ha hb
    | true =>
      simp only [d147265, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28148 q ha hb
  have h2 (q : Pattern) (ha : d147266 q = 1) (hb : d151525 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147266, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147266, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147267 q = 1) (hb : d151526 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147267, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147267, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147268 q = 1) (hb : d151665 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147268, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28148 q ha hb
    | true =>
      simp only [d147268, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h5 (q : Pattern) (ha : d147269 q = 1) (hb : d151666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147269, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147269, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147270 q = 1) (hb : d151667 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147270, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147270, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147271 q = 1) (hb : d151668 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147271, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147271, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147272 q = 1) (hb : d151669 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147272, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147272, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147273 q = 1) (hb : d151670 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147273, d151670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147273, d151670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147274 q = 1) (hb : d151671 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147274, d151671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147274, d151671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29710 (p : Pattern) (ha : d147278 p = 1) (hb : d151675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147268 q = 1) (hb : d151665 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147268, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28148 q ha hb
    | true =>
      simp only [d147268, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h2 (q : Pattern) (ha : d147269 q = 1) (hb : d151666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147269, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147269, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147270 q = 1) (hb : d151667 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147270, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147270, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147272 q = 1) (hb : d151669 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147272, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147272, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147277 q = 1) (hb : d151674 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147277, d151674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147277, d151674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147278 q = 1) (hb : d151675 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147278, d151675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147278, d151675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29711 (p : Pattern) (ha : d147284 p = 1) (hb : d151681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d151672 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29709 q ha hb
    | true =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d151673 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d151678 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147282 q = 1) (hb : d151679 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147282, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147282, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147283 q = 1) (hb : d151680 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147283, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147283, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147284 q = 1) (hb : d151681 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147284, d151681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147284, d151681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29712 (p : Pattern) (ha : d147288 p = 1) (hb : d151685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d151682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147286 q = 1) (hb : d151683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147286, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147286, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147287 q = 1) (hb : d151684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147287, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147287, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147288 q = 1) (hb : d151685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147288, d151685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147288, d151685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29713 (p : Pattern) (ha : d147294 p = 1) (hb : d151691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147289 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29711 q ha hb
    | true =>
      simp only [d147289, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29712 q ha hb
  have h2 (q : Pattern) (ha : d147290 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147290, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147290, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147291 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147291, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147291, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147292 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147292, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147292, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147293 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147293, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147293, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147294 q = 1) (hb : d151691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147294, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147294, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29714 (p : Pattern) (ha : d147297 p = 1) (hb : d151694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d151672 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29709 q ha hb
    | true =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d151673 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d151678 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147282 q = 1) (hb : d151679 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147282, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147282, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147283 q = 1) (hb : d151680 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147283, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147283, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147297 q = 1) (hb : d151694 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147297, d151694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147297, d151694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29715 (p : Pattern) (ha : d147298 p = 1) (hb : d151695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d151682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147286 q = 1) (hb : d151683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147286, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147286, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147287 q = 1) (hb : d151684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147287, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147287, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147298 q = 1) (hb : d151695 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147298, d151695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147298, d151695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29716 (p : Pattern) (ha : d147304 p = 1) (hb : d151701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147289 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29711 q ha hb
    | true =>
      simp only [d147289, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29712 q ha hb
  have h2 (q : Pattern) (ha : d147290 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147290, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147290, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147291 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147291, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147291, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147292 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147292, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147292, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147293 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147293, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147293, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147299 q = 1) (hb : d151696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29714 q ha hb
    | true =>
      simp only [d147299, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29715 q ha hb
  have h7 (q : Pattern) (ha : d147300 q = 1) (hb : d151697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147300, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147300, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147301 q = 1) (hb : d151698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147301, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147301, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147302 q = 1) (hb : d151699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147302, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147302, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147303 q = 1) (hb : d151700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147303, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147303, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147304 q = 1) (hb : d151701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147304, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147304, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29717 (p : Pattern) (ha : d147309 p = 1) (hb : d151706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d151672 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29709 q ha hb
    | true =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d151673 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d151678 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147282 q = 1) (hb : d151679 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147282, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147282, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147308 q = 1) (hb : d151705 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147308, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147308, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147309 q = 1) (hb : d151706 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147309, d151706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147309, d151706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29718 (p : Pattern) (ha : d147311 p = 1) (hb : d151708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d151682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147286 q = 1) (hb : d151683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147286, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147286, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147310 q = 1) (hb : d151707 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147310, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147310, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147311 q = 1) (hb : d151708 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147311, d151708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147311, d151708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29719 (p : Pattern) (ha : d147318 p = 1) (hb : d151715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d151672 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29709 q ha hb
    | true =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d151673 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d151678 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147316 q = 1) (hb : d151713 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147316, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147316, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147317 q = 1) (hb : d151714 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147317, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147317, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147318 q = 1) (hb : d151715 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147318, d151715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147318, d151715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29720 (p : Pattern) (ha : d147321 p = 1) (hb : d151718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d151682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147319 q = 1) (hb : d151716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147319, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147319, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147320 q = 1) (hb : d151717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147320, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147320, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147321 q = 1) (hb : d151718 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147321, d151718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147321, d151718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29721 (p : Pattern) (ha : d21188 p = 1) (hb : d147102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d52112 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9452 q = 1) (hb : d101067 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7946 q ha hb
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9464 q = 1) (hb : d101079 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9464, d101079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9464, d101079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9465 q = 1) (hb : d101080 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9465, d101080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9465, d101080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9466 q = 1) (hb : d101081 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9466, d101081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9466, d101081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21188 q = 1) (hb : d147102 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21188, d147102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21188, d147102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29722 (p : Pattern) (ha : d147341 p = 1) (hb : d151725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21189 q = 1) (hb : d147103 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29721 q ha hb
    | true =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21190 q = 1) (hb : d147104 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21191 q = 1) (hb : d147105 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d147105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d147105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21192 q = 1) (hb : d147106 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d147106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21192, d147106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21418 q = 1) (hb : d147262 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21418, d147262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21418, d147262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d147341 q = 1) (hb : d151725 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147341, d151725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147341, d151725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro29723 (p : Pattern) (ha : d147347 p = 1) (hb : d151731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147338 q = 1) (hb : d151722 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147338, d151722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28162 q ha hb
    | true =>
      simp only [d147338, d151722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28147 q ha hb
  have h2 (q : Pattern) (ha : d147339 q = 1) (hb : d151723 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147339, d151723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147339, d151723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147340 q = 1) (hb : d151724 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147340, d151724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147340, d151724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147342 q = 1) (hb : d151726 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147342, d151726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28147 q ha hb
    | true =>
      simp only [d147342, d151726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29722 q ha hb
  have h5 (q : Pattern) (ha : d147343 q = 1) (hb : d151727 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147343, d151727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147343, d151727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147344 q = 1) (hb : d151728 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147344, d151728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147344, d151728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147345 q = 1) (hb : d151729 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147345, d151729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147345, d151729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147265 q = 1) (hb : d151524 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147265, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28147 q ha hb
    | true =>
      simp only [d147265, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28148 q ha hb
  have h9 (q : Pattern) (ha : d147266 q = 1) (hb : d151525 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147266, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147266, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147267 q = 1) (hb : d151526 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147267, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147267, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147268 q = 1) (hb : d151665 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147268, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28148 q ha hb
    | true =>
      simp only [d147268, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h12 (q : Pattern) (ha : d147269 q = 1) (hb : d151666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147269, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147269, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147270 q = 1) (hb : d151667 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147270, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147270, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147271 q = 1) (hb : d151668 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147271, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147271, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147346 q = 1) (hb : d151730 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147346, d151730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147346, d151730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147347 q = 1) (hb : d151731 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147347, d151731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147347, d151731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro29724 (p : Pattern) (ha : d147353 p = 1) (hb : d151737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147348 q = 1) (hb : d151732 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147348, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29723 q ha hb
    | true =>
      simp only [d147348, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147349 q = 1) (hb : d151733 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147349, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147349, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147275 q = 1) (hb : d151672 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29709 q ha hb
    | true =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147276 q = 1) (hb : d151673 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147350 q = 1) (hb : d151734 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147350, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147350, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147351 q = 1) (hb : d151735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147351, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147351, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147352 q = 1) (hb : d151736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147352, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147352, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147353 q = 1) (hb : d151737 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147353, d151737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147353, d151737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29725 (p : Pattern) (ha : d147359 p = 1) (hb : d151743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d151672 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29709 q ha hb
    | true =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d151673 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147356 q = 1) (hb : d151740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147356, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147356, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147357 q = 1) (hb : d151741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147357, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147357, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147358 q = 1) (hb : d151742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147358, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147358, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147359 q = 1) (hb : d151743 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147359, d151743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147359, d151743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29726 (p : Pattern) (ha : d147365 p = 1) (hb : d151749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147312 q = 1) (hb : d151709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147312, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29717 q ha hb
    | true =>
      simp only [d147312, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29718 q ha hb
  have h2 (q : Pattern) (ha : d147313 q = 1) (hb : d151710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147313, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147313, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147314 q = 1) (hb : d151711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147314, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147314, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147315 q = 1) (hb : d151712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147315, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147315, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147322 q = 1) (hb : d151719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147322, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29719 q ha hb
    | true =>
      simp only [d147322, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29720 q ha hb
  have h6 (q : Pattern) (ha : d147323 q = 1) (hb : d151720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147323, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147323, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147324 q = 1) (hb : d151721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147324, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147324, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147354 q = 1) (hb : d151738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147354, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29724 q ha hb
    | true =>
      simp only [d147354, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29711 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147289 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147355 q = 1) (hb : d151739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147355, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147360 q = 1) (hb : d151744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147360, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29725 q ha hb
    | true =>
      simp only [d147360, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147361 q = 1) (hb : d151745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147361, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147361, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147362 q = 1) (hb : d151746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147362, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147363 q = 1) (hb : d151747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147363, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147364 q = 1) (hb : d151748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147364, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147365 q = 1) (hb : d151749 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147365, d151749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147365, d151749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro29727 (p : Pattern) (ha : d147366 p = 1) (hb : d151750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d151672 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29709 q ha hb
    | true =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d151673 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d151678 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147282 q = 1) (hb : d151679 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147282, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147282, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147308 q = 1) (hb : d151705 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147308, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147308, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147366 q = 1) (hb : d151750 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147366, d151750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147366, d151750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29728 (p : Pattern) (ha : d147367 p = 1) (hb : d151751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d151682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147286 q = 1) (hb : d151683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147286, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147286, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147310 q = 1) (hb : d151707 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147310, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147310, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147367 q = 1) (hb : d151751 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147367, d151751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147367, d151751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29729 (p : Pattern) (ha : d147372 p = 1) (hb : d151756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d151672 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29709 q ha hb
    | true =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d151673 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d151678 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147316 q = 1) (hb : d151713 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147316, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147316, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147317 q = 1) (hb : d151714 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147317, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147317, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147372 q = 1) (hb : d151756 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147372, d151756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147372, d151756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29730 (p : Pattern) (ha : d147373 p = 1) (hb : d151757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d151676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29710 q ha hb
    | true =>
      simp only [d147279, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d151677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d151682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147319 q = 1) (hb : d151716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147319, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147319, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147320 q = 1) (hb : d151717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147320, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147320, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147373 q = 1) (hb : d151757 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147373, d151757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147373, d151757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29731 (p : Pattern) (ha : d147377 p = 1) (hb : d151761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147348 q = 1) (hb : d151732 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147348, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29723 q ha hb
    | true =>
      simp only [d147348, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147349 q = 1) (hb : d151733 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147349, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147349, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147275 q = 1) (hb : d151672 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29709 q ha hb
    | true =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147276 q = 1) (hb : d151673 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147350 q = 1) (hb : d151734 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147350, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147350, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147351 q = 1) (hb : d151735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147351, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147351, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147352 q = 1) (hb : d151736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147352, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147352, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147377 q = 1) (hb : d151761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147377, d151761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147377, d151761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29732 (p : Pattern) (ha : d147380 p = 1) (hb : d151764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d151672 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29709 q ha hb
    | true =>
      simp only [d147275, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d151673 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147356 q = 1) (hb : d151740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147356, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147356, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147357 q = 1) (hb : d151741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147357, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147357, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147358 q = 1) (hb : d151742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147358, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147358, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147380 q = 1) (hb : d151764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147380, d151764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147380, d151764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29733 (p : Pattern) (ha : d147386 p = 1) (hb : d151770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147312 q = 1) (hb : d151709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147312, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29717 q ha hb
    | true =>
      simp only [d147312, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29718 q ha hb
  have h2 (q : Pattern) (ha : d147313 q = 1) (hb : d151710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147313, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147313, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147314 q = 1) (hb : d151711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147314, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147314, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147315 q = 1) (hb : d151712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147315, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147315, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147322 q = 1) (hb : d151719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147322, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29719 q ha hb
    | true =>
      simp only [d147322, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29720 q ha hb
  have h6 (q : Pattern) (ha : d147323 q = 1) (hb : d151720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147323, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147323, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147324 q = 1) (hb : d151721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147324, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147324, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147354 q = 1) (hb : d151738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147354, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29724 q ha hb
    | true =>
      simp only [d147354, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29711 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147289 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147355 q = 1) (hb : d151739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147355, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147360 q = 1) (hb : d151744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147360, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29725 q ha hb
    | true =>
      simp only [d147360, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147361 q = 1) (hb : d151745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147361, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147361, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147362 q = 1) (hb : d151746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147362, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147363 q = 1) (hb : d151747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147363, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147364 q = 1) (hb : d151748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147364, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147368 q = 1) (hb : d151752 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147368, d151752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29727 q ha hb
    | true =>
      simp only [d147368, d151752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29728 q ha hb
  have h17 (q : Pattern) (ha : d147369 q = 1) (hb : d151753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147369, d151753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147369, d151753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147370 q = 1) (hb : d151754 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147370, d151754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147370, d151754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d147371 q = 1) (hb : d151755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147371, d151755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147371, d151755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147374 q = 1) (hb : d151758 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147374, d151758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29729 q ha hb
    | true =>
      simp only [d147374, d151758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29730 q ha hb
  have h21 (q : Pattern) (ha : d147375 q = 1) (hb : d151759 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147375, d151759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147375, d151759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d147376 q = 1) (hb : d151760 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147376, d151760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147376, d151760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147378 q = 1) (hb : d151762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147378, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29731 q ha hb
    | true =>
      simp only [d147378, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29714 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d147299 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d147379 q = 1) (hb : d151763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d147379, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d147381 q = 1) (hb : d151765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147381, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29732 q ha hb
    | true =>
      simp only [d147381, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d147382 q = 1) (hb : d151766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147382, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d147382, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d147383 q = 1) (hb : d151767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d147383, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d147384 q = 1) (hb : d151768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147384, d151768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d147384, d151768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d147385 q = 1) (hb : d151769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147385, d151769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147385, d151769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d147386 q = 1) (hb : d151770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147386, d151770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147386, d151770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro29734 (p : Pattern) (ha : d147393 p = 1) (hb : d151777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147289 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29711 q ha hb
    | true =>
      simp only [d147289, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29712 q ha hb
  have h2 (q : Pattern) (ha : d147290 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147290, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147290, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147291 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147291, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147291, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147292 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147292, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147292, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147293 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147293, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147293, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147388 q = 1) (hb : d151772 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147388, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29712 q ha hb
    | true =>
      simp only [d147388, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147389 q = 1) (hb : d151773 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147389, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147389, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147390 q = 1) (hb : d151774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147390, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147390, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147391 q = 1) (hb : d151775 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147391, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147391, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147392 q = 1) (hb : d151776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147392, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147392, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147393 q = 1) (hb : d151777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147393, d151777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147393, d151777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29735 (p : Pattern) (ha : d147399 p = 1) (hb : d151783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147388 q = 1) (hb : d151772 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147388, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29712 q ha hb
    | true =>
      simp only [d147388, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147389 q = 1) (hb : d151773 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147389, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147389, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147390 q = 1) (hb : d151774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147390, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147390, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147391 q = 1) (hb : d151775 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147391, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147391, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147392 q = 1) (hb : d151776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147392, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147392, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147394 q = 1) (hb : d151778 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147394, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29715 q ha hb
    | true =>
      simp only [d147394, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147395 q = 1) (hb : d151779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147395, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147395, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147396 q = 1) (hb : d151780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147396, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147396, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147397 q = 1) (hb : d151781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147397, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147397, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147398 q = 1) (hb : d151782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147398, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147398, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147399 q = 1) (hb : d151783 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147399, d151783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147399, d151783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29736 (p : Pattern) (ha : d147406 p = 1) (hb : d151790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147378 q = 1) (hb : d151762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147378, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29731 q ha hb
    | true =>
      simp only [d147378, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29714 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147299 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147379 q = 1) (hb : d151763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147379, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147381 q = 1) (hb : d151765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147381, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29732 q ha hb
    | true =>
      simp only [d147381, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147382 q = 1) (hb : d151766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147382, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147382, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147383 q = 1) (hb : d151767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147383, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147404 q = 1) (hb : d151788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147404, d151788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147404, d151788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147405 q = 1) (hb : d151789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147405, d151789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147405, d151789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147406 q = 1) (hb : d151790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147406, d151790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147406, d151790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29737 (p : Pattern) (ha : d147408 p = 1) (hb : d151792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147394 q = 1) (hb : d151778 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147394, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29715 q ha hb
    | true =>
      simp only [d147394, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147395 q = 1) (hb : d151779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147395, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147395, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147396 q = 1) (hb : d151780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147396, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147396, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147397 q = 1) (hb : d151781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147397, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147397, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147398 q = 1) (hb : d151782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147398, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147398, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147408 q = 1) (hb : d151792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147408, d151792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147408, d151792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29738 (p : Pattern) (ha : d147430 p = 1) (hb : d151801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21314 q = 1) (hb : d147190 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d147190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d147190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29721 q ha hb
  have h2 (q : Pattern) (ha : d21189 q = 1) (hb : d147103 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29721 q ha hb
    | true =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21315 q = 1) (hb : d147191 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d147191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21315, d147191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21190 q = 1) (hb : d147104 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21316 q = 1) (hb : d147192 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d147192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21316, d147192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21317 q = 1) (hb : d147193 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d147193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21317, d147193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21623 q = 1) (hb : d147425 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21623, d147425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21623, d147425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147430 q = 1) (hb : d151801 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147430, d151801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d147430, d151801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro29739 (p : Pattern) (ha : d147444 p = 1) (hb : d151811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147427 q = 1) (hb : d151798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147427, d151798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28178 q ha hb
    | true =>
      simp only [d147427, d151798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28179 q ha hb
  have h2 (q : Pattern) (ha : d147428 q = 1) (hb : d151799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147428, d151799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147428, d151799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147429 q = 1) (hb : d151800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147429, d151800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147429, d151800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147431 q = 1) (hb : d151802 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147431, d151802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28179 q ha hb
    | true =>
      simp only [d147431, d151802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29738 q ha hb
  have h5 (q : Pattern) (ha : d147432 q = 1) (hb : d151803 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147432, d151803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147432, d151803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147433 q = 1) (hb : d151804 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147433, d151804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147433, d151804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147434 q = 1) (hb : d151805 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147434, d151805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147434, d151805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147436 q = 1) (hb : d151600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147436, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28179 q ha hb
    | true =>
      simp only [d147436, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28180 q ha hb
  have h9 (q : Pattern) (ha : d147437 q = 1) (hb : d151601 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147437, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147437, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147438 q = 1) (hb : d151602 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147438, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147438, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147439 q = 1) (hb : d151806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147439, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28180 q ha hb
    | true =>
      simp only [d147439, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h12 (q : Pattern) (ha : d147440 q = 1) (hb : d151807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147440, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147440, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147441 q = 1) (hb : d151808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147441, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147441, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147442 q = 1) (hb : d151809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147442, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147442, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147443 q = 1) (hb : d151810 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147443, d151810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147443, d151810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147444 q = 1) (hb : d151811 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147444, d151811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147444, d151811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro29740 (p : Pattern) (ha : d147449 p = 1) (hb : d151816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147436 q = 1) (hb : d151600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147436, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28179 q ha hb
    | true =>
      simp only [d147436, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28180 q ha hb
  have h2 (q : Pattern) (ha : d147437 q = 1) (hb : d151601 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147437, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147437, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147438 q = 1) (hb : d151602 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147438, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147438, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147439 q = 1) (hb : d151806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147439, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28180 q ha hb
    | true =>
      simp only [d147439, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h5 (q : Pattern) (ha : d147440 q = 1) (hb : d151807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147440, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147440, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147441 q = 1) (hb : d151808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147441, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147441, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147442 q = 1) (hb : d151809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147442, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147442, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147447 q = 1) (hb : d151814 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147447, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147447, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147448 q = 1) (hb : d151815 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147448, d151815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147448, d151815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147449 q = 1) (hb : d151816 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147449, d151816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147449, d151816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro29741 (p : Pattern) (ha : d147455 p = 1) (hb : d151822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147445 q = 1) (hb : d151812 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147445, d151812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29739 q ha hb
    | true =>
      simp only [d147445, d151812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147446 q = 1) (hb : d151813 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147446, d151813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147446, d151813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147450 q = 1) (hb : d151817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147450, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29740 q ha hb
    | true =>
      simp only [d147450, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147451 q = 1) (hb : d151818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147451, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147451, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147452 q = 1) (hb : d151819 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147452, d151819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147452, d151819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147453 q = 1) (hb : d151820 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147453, d151820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147453, d151820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147454 q = 1) (hb : d151821 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147454, d151821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147454, d151821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147455 q = 1) (hb : d151822 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147455, d151822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147455, d151822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29742 (p : Pattern) (ha : d147457 p = 1) (hb : d151824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147439 q = 1) (hb : d151806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147439, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28180 q ha hb
    | true =>
      simp only [d147439, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h2 (q : Pattern) (ha : d147440 q = 1) (hb : d151807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147440, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147440, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147441 q = 1) (hb : d151808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147441, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147441, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147447 q = 1) (hb : d151814 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147447, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147447, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147456 q = 1) (hb : d151823 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147456, d151823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147456, d151823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147457 q = 1) (hb : d151824 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147457, d151824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147457, d151824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29743 (p : Pattern) (ha : d147463 p = 1) (hb : d151830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147450 q = 1) (hb : d151817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147450, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29740 q ha hb
    | true =>
      simp only [d147450, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147451 q = 1) (hb : d151818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147451, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147451, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147458 q = 1) (hb : d151825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147458, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29742 q ha hb
    | true =>
      simp only [d147458, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147459 q = 1) (hb : d151826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147459, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147459, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147460 q = 1) (hb : d151827 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147460, d151827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147460, d151827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147461 q = 1) (hb : d151828 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147461, d151828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147461, d151828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147462 q = 1) (hb : d151829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147462, d151829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147462, d151829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147463 q = 1) (hb : d151830 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147463, d151830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147463, d151830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29744 (p : Pattern) (ha : d147474 p = 1) (hb : d151836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147450 q = 1) (hb : d151817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147450, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29740 q ha hb
    | true =>
      simp only [d147450, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147451 q = 1) (hb : d151818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147451, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147451, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147471 q = 1) (hb : d151833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147471, d151833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147471, d151833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147472 q = 1) (hb : d151834 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147472, d151834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147472, d151834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147473 q = 1) (hb : d151835 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147473, d151835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147473, d151835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147474 q = 1) (hb : d151836 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147474, d151836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147474, d151836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29745 (p : Pattern) (ha : d147480 p = 1) (hb : d151842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147464 q = 1) (hb : d151831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147464, d151831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29741 q ha hb
    | true =>
      simp only [d147464, d151831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29743 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147469 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147470 q = 1) (hb : d151832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147470, d151832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147470, d151832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147475 q = 1) (hb : d151837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147475, d151837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29744 q ha hb
    | true =>
      simp only [d147475, d151837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147476 q = 1) (hb : d151838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147476, d151838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147476, d151838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147477 q = 1) (hb : d151839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147477, d151839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147477, d151839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147478 q = 1) (hb : d151840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147478, d151840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147478, d151840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147479 q = 1) (hb : d151841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147479, d151841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147479, d151841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147480 q = 1) (hb : d151842 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147480, d151842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147480, d151842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29746 (p : Pattern) (ha : d147468 p = 1) (hb : d151847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147458 q = 1) (hb : d151825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147458, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29742 q ha hb
    | true =>
      simp only [d147458, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147459 q = 1) (hb : d151826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147459, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147459, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147465 q = 1) (hb : d151844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147465, d151844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147465, d151844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147466 q = 1) (hb : d151845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147466, d151845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147466, d151845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147467 q = 1) (hb : d151846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147467, d151846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147467, d151846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147468 q = 1) (hb : d151847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147468, d151847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147468, d151847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29747 (p : Pattern) (ha : d147487 p = 1) (hb : d151853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147482 q = 1) (hb : d151848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147482, d151848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29746 q ha hb
    | true =>
      simp only [d147482, d151848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147483 q = 1) (hb : d151849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147483, d151849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147483, d151849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147484 q = 1) (hb : d151850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147484, d151850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147484, d151850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147485 q = 1) (hb : d151851 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147485, d151851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147485, d151851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147486 q = 1) (hb : d151852 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147486, d151852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147486, d151852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147487 q = 1) (hb : d151853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147487, d151853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147487, d151853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29748 (p : Pattern) (ha : d147493 p = 1) (hb : d151859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147295 q = 1) (hb : d151692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147295, d151692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147295, d151692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29713 q ha hb
  have h2 (q : Pattern) (ha : d147296 q = 1) (hb : d151693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147296, d151693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147296, d151693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d147305 q = 1) (hb : d151702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147305, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29713 q ha hb
    | true =>
      simp only [d147305, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29716 q ha hb
  have h4 (q : Pattern) (ha : d147306 q = 1) (hb : d151703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147306, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147306, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147307 q = 1) (hb : d151704 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147307, d151704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147307, d151704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147387 q = 1) (hb : d151771 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147387, d151771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29726 q ha hb
    | true =>
      simp only [d147387, d151771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29733 q ha hb
  have h7 (q : Pattern) (ha : d147400 q = 1) (hb : d151784 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147400, d151784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29734 q ha hb
    | true =>
      simp only [d147400, d151784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29735 q ha hb
  have h8 (q : Pattern) (ha : d147401 q = 1) (hb : d151785 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147401, d151785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147401, d151785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147402 q = 1) (hb : d151786 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147402, d151786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147402, d151786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d147403 q = 1) (hb : d151787 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147403, d151787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147403, d151787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147407 q = 1) (hb : d151791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147407, d151791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147407, d151791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29736 q ha hb
  have h12 (q : Pattern) (ha : d147409 q = 1) (hb : d151793 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147409, d151793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147409, d151793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29737 q ha hb
  have h13 (q : Pattern) (ha : d147410 q = 1) (hb : d151794 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147410, d151794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147410, d151794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147411 q = 1) (hb : d151795 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147411, d151795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147411, d151795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d147412 q = 1) (hb : d151796 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147412, d151796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d147412, d151796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d147413 q = 1) (hb : d151797 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147413, d151797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147413, d151797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147481 q = 1) (hb : d151843 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147481, d151843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147481, d151843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29745 q ha hb
  have h18 (q : Pattern) (ha : d147488 q = 1) (hb : d151854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147488, d151854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147488, d151854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29747 q ha hb
  have h19 (q : Pattern) (ha : d147489 q = 1) (hb : d151855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147489, d151855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147489, d151855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147490 q = 1) (hb : d151856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147490, d151856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147490, d151856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d147491 q = 1) (hb : d151857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147491, d151857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d147491, d151857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d147492 q = 1) (hb : d151858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147492, d151858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147492, d151858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147493 q = 1) (hb : d151859 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147493, d151859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147493, d151859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29749 (p : Pattern) (ha : d147499 p = 1) (hb : d151865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147494 q = 1) (hb : d151860 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147494, d151860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147494, d151860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29748 q ha hb
  have h2 (q : Pattern) (ha : d147495 q = 1) (hb : d151861 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147495, d151861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147495, d151861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147496 q = 1) (hb : d151862 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147496, d151862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147496, d151862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147497 q = 1) (hb : d151863 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147497, d151863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147497, d151863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147498 q = 1) (hb : d151864 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147498, d151864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147498, d151864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147499 q = 1) (hb : d151865 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147499, d151865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147499, d151865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
