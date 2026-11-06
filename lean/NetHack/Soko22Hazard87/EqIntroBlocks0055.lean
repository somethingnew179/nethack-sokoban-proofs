import NetHack.Soko22Hazard87.EqIntroBlocks0054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro13750 (p : Pattern) (selected : d153008 p = 0) : d155084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152872 q = 0) : d154969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152873 q = 0) : d154970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152873, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152873, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152949 q = 0) : d155046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d152949, d155046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152949, d155046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153008 q = 0) : d155084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153008, d155084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153008, d155084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13751 (p : Pattern) (selected : d153013 p = 0) : d155089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152872 q = 0) : d154969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152955 q = 0) : d155052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152955, d155052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152955, d155052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152956 q = 0) : d155053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d152956, d155053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152956, d155053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153013 q = 0) : d155089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153013, d155089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153013, d155089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13752 (p : Pattern) (selected : d153017 p = 0) : d155093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152977 q = 0) : d155074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152978 q = 0) : d155075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152978, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152978, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152979 q = 0) : d155076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d152979, d155076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152979, d155076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153017 q = 0) : d155093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153017, d155093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153017, d155093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13753 (p : Pattern) (selected : d153019 p = 0) : d154979 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152996 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152996, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13747 q selected
    | true =>
      simp only [d152996, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152997 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152997, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152997, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152998 q = 0) : d154969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152998, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152998, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152999 q = 0) : d154970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152999, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152999, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153000 q = 0) : d154971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153000, d154971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153000, d154971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153019 q = 0) : d154979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153019, d154979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153019, d154979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13754 (p : Pattern) (selected : d153025 p = 0) : d155099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152951 q = 0) : d155048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152951, d155048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13739 q selected
    | true =>
      simp only [d152951, d155048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152952 q = 0) : d155049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152952, d155049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152952, d155049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152953 q = 0) : d155050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152953, d155050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152953, d155050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152954 q = 0) : d155051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152954, d155051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152954, d155051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152958 q = 0) : d155055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152958, d155055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13740 q selected
    | true =>
      simp only [d152958, d155055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152959 q = 0) : d155056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152959, d155056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152959, d155056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d152960 q = 0) : d155057 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152960, d155057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152960, d155057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d152981 q = 0) : d155078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152981, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13744 q selected
    | true =>
      simp only [d152981, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
  have h9 (q : Pattern) (selected : d153002 q = 0) : d154973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153002, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13748 q selected
    | true =>
      simp only [d153002, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d153003 q = 0) : d155079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153003, d155079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153003, d155079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d152876 q = 0) : d154973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
    | true =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d152877 q = 0) : d154974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152877, d154974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d152877, d154974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153004 q = 0) : d155080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153004, d155080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153004, d155080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153005 q = 0) : d155081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153005, d155081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153005, d155081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153006 q = 0) : d155082 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153006, d155082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153006, d155082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153009 q = 0) : d155085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153009, d155085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13750 q selected
    | true =>
      simp only [d153009, d155085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d153010 q = 0) : d155086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153010, d155086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153010, d155086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d153011 q = 0) : d155087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153011, d155087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d153011, d155087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d153012 q = 0) : d155088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153012, d155088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153012, d155088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d153014 q = 0) : d155090 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153014, d155090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13751 q selected
    | true =>
      simp only [d153014, d155090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d153015 q = 0) : d155091 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153015, d155091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153015, d155091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d153016 q = 0) : d155092 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153016, d155092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153016, d155092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d153018 q = 0) : d155094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153018, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13752 q selected
    | true =>
      simp only [d153018, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13729 q selected
  have h24 (q : Pattern) (selected : d153020 q = 0) : d154980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153020, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13753 q selected
    | true =>
      simp only [d153020, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d153021 q = 0) : d155095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153021, d155095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d153021, d155095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d152883 q = 0) : d154980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13729 q selected
    | true =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d152884 q = 0) : d154981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152884, d154981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d152884, d154981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d153022 q = 0) : d155096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153022, d155096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d153022, d155096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d153023 q = 0) : d155097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153023, d155097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d153023, d155097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d153024 q = 0) : d155098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153024, d155098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153024, d155098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d153025 q = 0) : d155099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153025, d155099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153025, d155099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro13755 (p : Pattern) (selected : d153027 p = 0) : d155101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152876 q = 0) : d154973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
    | true =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152934 q = 0) : d155031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152934, d155031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152934, d155031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152935 q = 0) : d155032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152935, d155032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152935, d155032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152936 q = 0) : d155033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152936, d155033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152936, d155033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152937 q = 0) : d155034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152937, d155034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152937, d155034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153027 q = 0) : d155101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153027, d155101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153027, d155101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13756 (p : Pattern) (selected : d153034 p = 0) : d155108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153018 q = 0) : d155094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153018, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13752 q selected
    | true =>
      simp only [d153018, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13729 q selected
  have h2 (q : Pattern) (selected : d153020 q = 0) : d154980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153020, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13753 q selected
    | true =>
      simp only [d153020, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153021 q = 0) : d155095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153021, d155095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153021, d155095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152883 q = 0) : d154980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13729 q selected
    | true =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152884 q = 0) : d154981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152884, d154981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152884, d154981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153022 q = 0) : d155096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153022, d155096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153022, d155096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153032 q = 0) : d155106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153032, d155106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153032, d155106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153033 q = 0) : d155107 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153033, d155107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153033, d155107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153034 q = 0) : d155108 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153034, d155108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153034, d155108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13757 (p : Pattern) (selected : d153045 p = 0) : d155119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153040 q = 0) : d155114 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153040, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153040, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13741 q selected
  have h2 (q : Pattern) (selected : d152963 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13741 q selected
    | true =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153041 q = 0) : d155115 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153041, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153041, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152964 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153042 q = 0) : d155116 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153042, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153042, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153043 q = 0) : d155117 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153043, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153043, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152899 q = 0) : d154996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152899, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152899, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
  have h8 (q : Pattern) (selected : d152858 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
    | true =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152900 q = 0) : d154997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152900, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152900, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152859 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d152901 q = 0) : d154998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152901, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d152901, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d152902 q = 0) : d154999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152902, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d152902, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153044 q = 0) : d155118 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153044, d155118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153044, d155118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d152903 q = 0) : d155000 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152903, d155000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d152903, d155000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153045 q = 0) : d155119 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153045, d155119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153045, d155119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13758 (p : Pattern) (selected : d153051 p = 0) : d155125 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153046 q = 0) : d155120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13757 q selected
    | true =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13732 q selected
  have h2 (q : Pattern) (selected : d153047 q = 0) : d155121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153048 q = 0) : d155122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152905 q = 0) : d155002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152905, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13732 q selected
    | true =>
      simp only [d152905, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152906 q = 0) : d155003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152906, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152906, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152907 q = 0) : d155004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152907, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152907, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153049 q = 0) : d155123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153049, d155123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153049, d155123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152908 q = 0) : d155005 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152908, d155005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152908, d155005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153050 q = 0) : d155124 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153050, d155124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153050, d155124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153051 q = 0) : d155125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153051, d155125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153051, d155125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13759 (p : Pattern) (selected : d153057 p = 0) : d155131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153052 q = 0) : d155126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153052, d155126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13758 q selected
    | true =>
      simp only [d153052, d155126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153053 q = 0) : d155127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153053, d155127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153053, d155127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152911 q = 0) : d155008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152911, d155008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13733 q selected
    | true =>
      simp only [d152911, d155008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152912 q = 0) : d155009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152912, d155009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152912, d155009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153054 q = 0) : d155128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153054, d155128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153054, d155128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153055 q = 0) : d155129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153055, d155129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153055, d155129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153056 q = 0) : d155130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153056, d155130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153056, d155130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153057 q = 0) : d155131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153057, d155131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153057, d155131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13760 (p : Pattern) (selected : d153064 p = 0) : d155001 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153059 q = 0) : d154996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153059, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153059, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13745 q selected
  have h2 (q : Pattern) (selected : d152984 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13745 q selected
    | true =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153060 q = 0) : d154997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153060, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153060, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152985 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153061 q = 0) : d154998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153061, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153061, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153062 q = 0) : d154999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153062, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153062, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153063 q = 0) : d155000 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153063, d155000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153063, d155000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153064 q = 0) : d155001 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153064, d155001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153064, d155001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13761 (p : Pattern) (selected : d153070 p = 0) : d155007 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153065 q = 0) : d155002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153065, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13760 q selected
    | true =>
      simp only [d153065, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153066 q = 0) : d155003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153066, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153066, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153067 q = 0) : d155004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153067, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153067, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153068 q = 0) : d155005 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153068, d155005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153068, d155005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153069 q = 0) : d155006 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153069, d155006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153069, d155006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153070 q = 0) : d155007 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153070, d155007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153070, d155007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13762 (p : Pattern) (selected : d153076 p = 0) : d155013 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153071 q = 0) : d155008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153071, d155008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13761 q selected
    | true =>
      simp only [d153071, d155008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153072 q = 0) : d155009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153072, d155009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153072, d155009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153073 q = 0) : d155010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153073, d155010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153073, d155010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153074 q = 0) : d155011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153074, d155011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153074, d155011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153075 q = 0) : d155012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153075, d155012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153075, d155012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153076 q = 0) : d155013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153076, d155013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153076, d155013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13763 (p : Pattern) (selected : d153082 p = 0) : d155137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153058 q = 0) : d155132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153058, d155132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13759 q selected
    | true =>
      simp only [d153058, d155132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13734 q selected
  have h2 (q : Pattern) (selected : d153077 q = 0) : d155014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153077, d155014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13762 q selected
    | true =>
      simp only [d153077, d155014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153078 q = 0) : d155133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153078, d155133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153078, d155133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152917 q = 0) : d155014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152917, d155014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13734 q selected
    | true =>
      simp only [d152917, d155014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152918 q = 0) : d155015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152918, d155015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152918, d155015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153079 q = 0) : d155134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153079, d155134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153079, d155134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153080 q = 0) : d155135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153080, d155135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153080, d155135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153081 q = 0) : d155136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153081, d155136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153081, d155136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153082 q = 0) : d155137 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153082, d155137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153082, d155137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13764 (p : Pattern) (selected : d153088 p = 0) : d155143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152939 q = 0) : d155036 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d152939, d155036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152939, d155036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13737 q selected
  have h2 (q : Pattern) (selected : d152940 q = 0) : d155037 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d152940, d155037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152940, d155037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152946 q = 0) : d155043 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d152946, d155043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13737 q selected
    | true =>
      simp only [d152946, d155043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13738 q selected
  have h4 (q : Pattern) (selected : d152947 q = 0) : d155044 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d152947, d155044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152947, d155044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152948 q = 0) : d155045 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d152948, d155045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152948, d155045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153026 q = 0) : d155100 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153026, d155100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13749 q selected
    | true =>
      simp only [d153026, d155100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13754 q selected
  have h7 (q : Pattern) (selected : d153028 q = 0) : d155102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153028, d155102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13755 q selected
    | true =>
      simp only [d153028, d155102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153029 q = 0) : d155103 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153029, d155103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153029, d155103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153030 q = 0) : d155104 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153030, d155104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153030, d155104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d153031 q = 0) : d155105 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153031, d155105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153031, d155105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153035 q = 0) : d155109 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153035, d155109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153035, d155109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13756 q selected
  have h12 (q : Pattern) (selected : d153036 q = 0) : d155110 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153036, d155110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153036, d155110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153037 q = 0) : d155111 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153037, d155111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153037, d155111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d153038 q = 0) : d155112 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153038, d155112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153038, d155112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153039 q = 0) : d155113 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153039, d155113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153039, d155113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153083 q = 0) : d155138 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153083, d155138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153083, d155138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13763 q selected
  have h17 (q : Pattern) (selected : d153084 q = 0) : d155139 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153084, d155139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153084, d155139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153085 q = 0) : d155140 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153085, d155140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d153085, d155140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d153086 q = 0) : d155141 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153086, d155141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153086, d155141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153087 q = 0) : d155142 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153087, d155142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153087, d155142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d153088 q = 0) : d155143 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d153088, d155143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153088, d155143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro13765 (p : Pattern) (selected : d153094 p = 0) : d155149 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152929 q = 0) : d155026 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d152929, d155026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152929, d155026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13736 q selected
  have h2 (q : Pattern) (selected : d152930 q = 0) : d155027 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d152930, d155027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152930, d155027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152931 q = 0) : d155028 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d152931, d155028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152931, d155028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152932 q = 0) : d155029 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d152932, d155029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152932, d155029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152933 q = 0) : d155030 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d152933, d155030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152933, d155030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153089 q = 0) : d155144 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d153089, d155144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153089, d155144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13764 q selected
  have h7 (q : Pattern) (selected : d153090 q = 0) : d155145 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d153090, d155145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153090, d155145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153091 q = 0) : d155146 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d153091, d155146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153091, d155146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153092 q = 0) : d155147 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d153092, d155147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153092, d155147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153093 q = 0) : d155148 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d153093, d155148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153093, d155148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153094 q = 0) : d155149 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d153094, d155149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153094, d155149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13766 (p : Pattern) (selected : d153099 p = 0) : d155154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152981 q = 0) : d155078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152981, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13744 q selected
    | true =>
      simp only [d152981, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
  have h2 (q : Pattern) (selected : d153095 q = 0) : d155150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153095, d155150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153095, d155150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153096 q = 0) : d155151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153096, d155151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153096, d155151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153097 q = 0) : d155152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153097, d155152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153097, d155152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153098 q = 0) : d155153 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153098, d155153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153098, d155153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153099 q = 0) : d155154 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153099, d155154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153099, d155154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13767 (p : Pattern) (selected : d153106 p = 0) : d155161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152981 q = 0) : d155078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152981, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13744 q selected
    | true =>
      simp only [d152981, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
  have h2 (q : Pattern) (selected : d153095 q = 0) : d155150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153095, d155150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153095, d155150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153096 q = 0) : d155151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153096, d155151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153096, d155151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153097 q = 0) : d155152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153097, d155152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153097, d155152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153098 q = 0) : d155153 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153098, d155153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153098, d155153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153018 q = 0) : d155094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153018, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13752 q selected
    | true =>
      simp only [d153018, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13729 q selected
  have h7 (q : Pattern) (selected : d153102 q = 0) : d155157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153102, d155157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153102, d155157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153103 q = 0) : d155158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153103, d155158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153103, d155158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153104 q = 0) : d155159 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153104, d155159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153104, d155159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153105 q = 0) : d155160 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153105, d155160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153105, d155160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153106 q = 0) : d155161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153106, d155161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153106, d155161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13768 (p : Pattern) (selected : d153111 p = 0) : d155166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152977 q = 0) : d155074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152978 q = 0) : d155075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152978, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152978, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153110 q = 0) : d155165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153110, d155165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153110, d155165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153111 q = 0) : d155166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153111, d155166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153111, d155166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13769 (p : Pattern) (selected : d153118 p = 0) : d155173 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152977 q = 0) : d155074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153116 q = 0) : d155171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153116, d155171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153116, d155171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153117 q = 0) : d155172 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153117, d155172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153117, d155172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153118 q = 0) : d155173 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153118, d155173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153118, d155173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13770 (p : Pattern) (selected : d153123 p = 0) : d155178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d313 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153122 q = 0) : d155177 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153122, d155177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153122, d155177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153123 q = 0) : d155178 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153123, d155178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153123, d155178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13771 (p : Pattern) (selected : d153130 p = 0) : d155185 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9452 q = 0) : d101067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2798 q selected
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9453 q = 0) : d101068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153129 q = 0) : d155184 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153129, d155184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153129, d155184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153130 q = 0) : d155185 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153130, d155185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153130, d155185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro13772 (p : Pattern) (selected : d153136 p = 0) : d155191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153124 q = 0) : d155179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153124, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13770 q selected
    | true =>
      simp only [d153124, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153125 q = 0) : d155180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153125, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153125, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153126 q = 0) : d155181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153126, d155181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153126, d155181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153127 q = 0) : d155182 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153127, d155182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153127, d155182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152963 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13741 q selected
    | true =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152964 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152965 q = 0) : d155062 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152965, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152965, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152966 q = 0) : d155063 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152966, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152966, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153128 q = 0) : d155183 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153128, d155183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153128, d155183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153133 q = 0) : d155188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153134 q = 0) : d155189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d152858 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
    | true =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d152859 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d152860 q = 0) : d154957 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152860, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152860, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d152861 q = 0) : d154958 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152861, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d152861, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153135 q = 0) : d155190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153135, d155190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153135, d155190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153136 q = 0) : d155191 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153136, d155191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153136, d155191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro13773 (p : Pattern) (selected : d153142 p = 0) : d155197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153137 q = 0) : d155192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153137, d155192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13772 q selected
    | true =>
      simp only [d153137, d155192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13742 q selected
  have h2 (q : Pattern) (selected : d153138 q = 0) : d155193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153138, d155193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153138, d155193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153139 q = 0) : d155194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153139, d155194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153139, d155194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152969 q = 0) : d155066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13742 q selected
    | true =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13725 q selected
  have h5 (q : Pattern) (selected : d152970 q = 0) : d155067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152971 q = 0) : d155068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153140 q = 0) : d155195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153140, d155195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153140, d155195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152864 q = 0) : d154961 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152864, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13725 q selected
    | true =>
      simp only [d152864, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152865 q = 0) : d154962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152865, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152865, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152866 q = 0) : d154963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152866, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152866, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d152972 q = 0) : d155069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152972, d155069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152972, d155069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153141 q = 0) : d155196 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153141, d155196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153141, d155196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153142 q = 0) : d155197 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153142, d155197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153142, d155197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13774 (p : Pattern) (selected : d153148 p = 0) : d155203 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153143 q = 0) : d155198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153143, d155198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13773 q selected
    | true =>
      simp only [d153143, d155198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153144 q = 0) : d155199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153144, d155199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153144, d155199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153145 q = 0) : d155200 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153145, d155200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153145, d155200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153146 q = 0) : d155201 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153146, d155201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153146, d155201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153147 q = 0) : d155202 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153147, d155202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153147, d155202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153148 q = 0) : d155203 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153148, d155203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153148, d155203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13775 (p : Pattern) (selected : d153151 p = 0) : d155059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d344 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153150 q = 0) : d155058 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153150, d155058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153150, d155058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153151 q = 0) : d155059 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153151, d155059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153151, d155059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13776 (p : Pattern) (selected : d153157 p = 0) : d155065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153152 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13775 q selected
    | true =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153153 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153154 q = 0) : d155062 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153154, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153154, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153155 q = 0) : d155063 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153155, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153155, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152984 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13745 q selected
    | true =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152985 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152986 q = 0) : d154957 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152986, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152986, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152987 q = 0) : d154958 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152987, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152987, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153156 q = 0) : d155064 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153156, d155064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153156, d155064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152988 q = 0) : d154959 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152988, d154959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d152988, d154959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153157 q = 0) : d155065 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153157, d155065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153157, d155065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13777 (p : Pattern) (selected : d153163 p = 0) : d155071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153158 q = 0) : d155066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153158, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13776 q selected
    | true =>
      simp only [d153158, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13746 q selected
  have h2 (q : Pattern) (selected : d153159 q = 0) : d155067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153159, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153159, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153160 q = 0) : d155068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153160, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153160, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152990 q = 0) : d154961 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152990, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13746 q selected
    | true =>
      simp only [d152990, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152991 q = 0) : d154962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152991, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152991, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152992 q = 0) : d154963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152992, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152992, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153161 q = 0) : d155069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153161, d155069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153161, d155069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152993 q = 0) : d154964 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152993, d154964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152993, d154964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153162 q = 0) : d155070 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153162, d155070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153162, d155070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153163 q = 0) : d155071 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153163, d155071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153163, d155071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13778 (p : Pattern) (selected : d153169 p = 0) : d155077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153164 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153164, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13777 q selected
    | true =>
      simp only [d153164, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153165 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153165, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153165, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152996 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152996, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13747 q selected
    | true =>
      simp only [d152996, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152997 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152997, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152997, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153166 q = 0) : d155074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153166, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153166, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153167 q = 0) : d155075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153167, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153167, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153168 q = 0) : d155076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153168, d155076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153168, d155076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153169 q = 0) : d155077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153169, d155077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153169, d155077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13779 (p : Pattern) (selected : d153175 p = 0) : d155209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153172 q = 0) : d155206 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153172, d155206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153172, d155206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153173 q = 0) : d155207 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153173, d155207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153173, d155207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153174 q = 0) : d155208 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153174, d155208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153174, d155208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153175 q = 0) : d155209 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153175, d155209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153175, d155209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13780 (p : Pattern) (selected : d153181 p = 0) : d155215 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153112 q = 0) : d155167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153112, d155167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13768 q selected
    | true =>
      simp only [d153112, d155167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13739 q selected
  have h2 (q : Pattern) (selected : d153113 q = 0) : d155168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153113, d155168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153113, d155168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153114 q = 0) : d155169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153114, d155169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153114, d155169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153115 q = 0) : d155170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153115, d155170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153115, d155170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153119 q = 0) : d155174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153119, d155174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13769 q selected
    | true =>
      simp only [d153119, d155174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13740 q selected
  have h6 (q : Pattern) (selected : d153120 q = 0) : d155175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153120, d155175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153120, d155175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153121 q = 0) : d155176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153121, d155176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153121, d155176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153149 q = 0) : d155204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153149, d155204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13774 q selected
    | true =>
      simp only [d153149, d155204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13744 q selected
  have h9 (q : Pattern) (selected : d153170 q = 0) : d155078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153170, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13778 q selected
    | true =>
      simp only [d153170, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13748 q selected
  have h10 (q : Pattern) (selected : d153171 q = 0) : d155205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153171, d155205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153171, d155205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153176 q = 0) : d155210 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153176, d155210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13779 q selected
    | true =>
      simp only [d153176, d155210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153177 q = 0) : d155211 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153177, d155211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153177, d155211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153178 q = 0) : d155212 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153178, d155212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153178, d155212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153179 q = 0) : d155213 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153179, d155213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153179, d155213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153180 q = 0) : d155214 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153180, d155214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153180, d155214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153181 q = 0) : d155215 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153181, d155215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153181, d155215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro13781 (p : Pattern) (selected : d153182 p = 0) : d155216 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152977 q = 0) : d155074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152978 q = 0) : d155075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152978, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152978, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153110 q = 0) : d155165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153110, d155165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153110, d155165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153182 q = 0) : d155216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153182, d155216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153182, d155216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13782 (p : Pattern) (selected : d153187 p = 0) : d155221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152977 q = 0) : d155074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153116 q = 0) : d155171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153116, d155171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153116, d155171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153117 q = 0) : d155172 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153117, d155172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153117, d155172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153187 q = 0) : d155221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153187, d155221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153187, d155221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13783 (p : Pattern) (selected : d153191 p = 0) : d155225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153143 q = 0) : d155198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153143, d155198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13773 q selected
    | true =>
      simp only [d153143, d155198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153144 q = 0) : d155199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153144, d155199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153144, d155199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153145 q = 0) : d155200 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153145, d155200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153145, d155200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153146 q = 0) : d155201 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153146, d155201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153146, d155201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153147 q = 0) : d155202 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153147, d155202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153147, d155202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153191 q = 0) : d155225 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153191, d155225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153191, d155225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13784 (p : Pattern) (selected : d153193 p = 0) : d155093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153164 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153164, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13777 q selected
    | true =>
      simp only [d153164, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153165 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153165, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153165, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152996 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152996, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13747 q selected
    | true =>
      simp only [d152996, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152997 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152997, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152997, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153166 q = 0) : d155074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153166, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153166, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153167 q = 0) : d155075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153167, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153167, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153168 q = 0) : d155076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153168, d155076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153168, d155076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153193 q = 0) : d155093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153193, d155093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153193, d155093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13785 (p : Pattern) (selected : d153196 p = 0) : d155228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153172 q = 0) : d155206 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153172, d155206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153172, d155206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153173 q = 0) : d155207 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153173, d155207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153173, d155207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153174 q = 0) : d155208 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153174, d155208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153174, d155208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153196 q = 0) : d155228 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153196, d155228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153196, d155228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13786 (p : Pattern) (selected : d153202 p = 0) : d155234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153112 q = 0) : d155167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153112, d155167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13768 q selected
    | true =>
      simp only [d153112, d155167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13739 q selected
  have h2 (q : Pattern) (selected : d153113 q = 0) : d155168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153113, d155168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153113, d155168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153114 q = 0) : d155169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153114, d155169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153114, d155169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153115 q = 0) : d155170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153115, d155170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153115, d155170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153119 q = 0) : d155174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153119, d155174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13769 q selected
    | true =>
      simp only [d153119, d155174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13740 q selected
  have h6 (q : Pattern) (selected : d153120 q = 0) : d155175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153120, d155175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153120, d155175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153121 q = 0) : d155176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153121, d155176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153121, d155176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153149 q = 0) : d155204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153149, d155204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13774 q selected
    | true =>
      simp only [d153149, d155204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13744 q selected
  have h9 (q : Pattern) (selected : d153170 q = 0) : d155078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153170, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13778 q selected
    | true =>
      simp only [d153170, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13748 q selected
  have h10 (q : Pattern) (selected : d153171 q = 0) : d155205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153171, d155205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153171, d155205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153176 q = 0) : d155210 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153176, d155210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13779 q selected
    | true =>
      simp only [d153176, d155210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153177 q = 0) : d155211 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153177, d155211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153177, d155211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153178 q = 0) : d155212 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153178, d155212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153178, d155212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153179 q = 0) : d155213 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153179, d155213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153179, d155213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153180 q = 0) : d155214 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153180, d155214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153180, d155214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153183 q = 0) : d155217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153183, d155217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13781 q selected
    | true =>
      simp only [d153183, d155217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13750 q selected
  have h17 (q : Pattern) (selected : d153184 q = 0) : d155218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153184, d155218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153184, d155218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d153185 q = 0) : d155219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153185, d155219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d153185, d155219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d153186 q = 0) : d155220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153186, d155220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153186, d155220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d153188 q = 0) : d155222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153188, d155222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13782 q selected
    | true =>
      simp only [d153188, d155222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13751 q selected
  have h21 (q : Pattern) (selected : d153189 q = 0) : d155223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153189, d155223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153189, d155223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d153190 q = 0) : d155224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153190, d155224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153190, d155224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d153192 q = 0) : d155226 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153192, d155226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13783 q selected
    | true =>
      simp only [d153192, d155226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13752 q selected
  have h24 (q : Pattern) (selected : d153194 q = 0) : d155094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153194, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13784 q selected
    | true =>
      simp only [d153194, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13753 q selected
  have h25 (q : Pattern) (selected : d153195 q = 0) : d155227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153195, d155227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d153195, d155227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d153197 q = 0) : d155229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153197, d155229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13785 q selected
    | true =>
      simp only [d153197, d155229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d153198 q = 0) : d155230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153198, d155230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d153198, d155230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d153199 q = 0) : d155231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153199, d155231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d153199, d155231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d153200 q = 0) : d155232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153200, d155232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d153200, d155232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d153201 q = 0) : d155233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153201, d155233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153201, d155233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d153202 q = 0) : d155234 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153202, d155234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153202, d155234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro13787 (p : Pattern) (selected : d153204 p = 0) : d155236 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152981 q = 0) : d155078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152981, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13744 q selected
    | true =>
      simp only [d152981, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
  have h2 (q : Pattern) (selected : d153095 q = 0) : d155150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153095, d155150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153095, d155150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153096 q = 0) : d155151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153096, d155151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153096, d155151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153097 q = 0) : d155152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153097, d155152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153097, d155152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153098 q = 0) : d155153 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153098, d155153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153098, d155153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152876 q = 0) : d154973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
    | true =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152934 q = 0) : d155031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152934, d155031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152934, d155031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152935 q = 0) : d155032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152935, d155032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152935, d155032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152936 q = 0) : d155033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152936, d155033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152936, d155033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152937 q = 0) : d155034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152937, d155034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152937, d155034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153204 q = 0) : d155236 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153204, d155236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153204, d155236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13788 (p : Pattern) (selected : d153211 p = 0) : d155243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153192 q = 0) : d155226 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153192, d155226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13783 q selected
    | true =>
      simp only [d153192, d155226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13752 q selected
  have h2 (q : Pattern) (selected : d153194 q = 0) : d155094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153194, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13784 q selected
    | true =>
      simp only [d153194, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13753 q selected
  have h3 (q : Pattern) (selected : d153195 q = 0) : d155227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153195, d155227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153195, d155227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153197 q = 0) : d155229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153197, d155229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13785 q selected
    | true =>
      simp only [d153197, d155229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153198 q = 0) : d155230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153198, d155230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153198, d155230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153199 q = 0) : d155231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153199, d155231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153199, d155231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153209 q = 0) : d155241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153209, d155241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153209, d155241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153210 q = 0) : d155242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153210, d155242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153210, d155242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153211 q = 0) : d155243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153211, d155243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153211, d155243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13789 (p : Pattern) (selected : d153213 p = 0) : d155245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152883 q = 0) : d154980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13729 q selected
    | true =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152941 q = 0) : d155038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152941, d155038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152941, d155038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152942 q = 0) : d155039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152942, d155039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152942, d155039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152943 q = 0) : d155040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152943, d155040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152943, d155040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152944 q = 0) : d155041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152944, d155041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152944, d155041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153213 q = 0) : d155245 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153213, d155245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153213, d155245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13790 (p : Pattern) (selected : d153229 p = 0) : d155261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153219 q = 0) : d155251 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153219, d155251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153219, d155251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13770 q selected
  have h2 (q : Pattern) (selected : d153124 q = 0) : d155179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153124, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13770 q selected
    | true =>
      simp only [d153124, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153220 q = 0) : d155252 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153220, d155252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153220, d155252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153125 q = 0) : d155180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153125, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153125, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153221 q = 0) : d155253 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153221, d155253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153221, d155253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153222 q = 0) : d155254 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153222, d155254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153222, d155254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153040 q = 0) : d155114 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153040, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153040, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13741 q selected
  have h8 (q : Pattern) (selected : d152963 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13741 q selected
    | true =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153041 q = 0) : d155115 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153041, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153041, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152964 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153042 q = 0) : d155116 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153042, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153042, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153043 q = 0) : d155117 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153043, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153043, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153223 q = 0) : d155255 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153223, d155255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153223, d155255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153224 q = 0) : d155256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
  have h15 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153225 q = 0) : d155257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153226 q = 0) : d155258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153227 q = 0) : d155259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d152899 q = 0) : d154996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152899, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152899, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
  have h21 (q : Pattern) (selected : d152858 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
    | true =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d152900 q = 0) : d154997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152900, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d152900, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d152859 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d152901 q = 0) : d154998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152901, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d152901, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d152902 q = 0) : d154999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152902, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d152902, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d153228 q = 0) : d155260 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153228, d155260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153228, d155260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d153229 q = 0) : d155261 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153229, d155261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153229, d155261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro13791 (p : Pattern) (selected : d153235 p = 0) : d155267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153230 q = 0) : d155262 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153230, d155262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13790 q selected
    | true =>
      simp only [d153230, d155262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13757 q selected
  have h2 (q : Pattern) (selected : d153231 q = 0) : d155263 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153231, d155263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153231, d155263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153232 q = 0) : d155264 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153232, d155264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153232, d155264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153046 q = 0) : d155120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13757 q selected
    | true =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13732 q selected
  have h5 (q : Pattern) (selected : d153047 q = 0) : d155121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153048 q = 0) : d155122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153233 q = 0) : d155265 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153233, d155265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153233, d155265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152905 q = 0) : d155002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152905, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13732 q selected
    | true =>
      simp only [d152905, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152906 q = 0) : d155003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152906, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152906, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152907 q = 0) : d155004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152907, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152907, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153049 q = 0) : d155123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153049, d155123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153049, d155123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153234 q = 0) : d155266 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153234, d155266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153234, d155266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153235 q = 0) : d155267 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153235, d155267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153235, d155267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13792 (p : Pattern) (selected : d153241 p = 0) : d155273 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153236 q = 0) : d155268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153236, d155268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13791 q selected
    | true =>
      simp only [d153236, d155268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153237 q = 0) : d155269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153237, d155269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153237, d155269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153052 q = 0) : d155126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153052, d155126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13758 q selected
    | true =>
      simp only [d153052, d155126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153053 q = 0) : d155127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153053, d155127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153053, d155127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153238 q = 0) : d155270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153238, d155270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153238, d155270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153239 q = 0) : d155271 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153239, d155271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153239, d155271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153240 q = 0) : d155272 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153240, d155272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153240, d155272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153241 q = 0) : d155273 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153241, d155273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153241, d155273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13793 (p : Pattern) (selected : d153248 p = 0) : d155119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153243 q = 0) : d155114 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153243, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153243, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13775 q selected
  have h2 (q : Pattern) (selected : d153152 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13775 q selected
    | true =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153244 q = 0) : d155115 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153244, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153244, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153153 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153245 q = 0) : d155116 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153245, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153245, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153246 q = 0) : d155117 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153246, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153246, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153059 q = 0) : d154996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153059, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153059, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13745 q selected
  have h8 (q : Pattern) (selected : d152984 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13745 q selected
    | true =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153060 q = 0) : d154997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153060, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153060, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152985 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153061 q = 0) : d154998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153061, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153061, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153062 q = 0) : d154999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153062, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153062, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153247 q = 0) : d155118 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153247, d155118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153247, d155118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153063 q = 0) : d155000 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153063, d155000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153063, d155000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153248 q = 0) : d155119 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153248, d155119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153248, d155119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13794 (p : Pattern) (selected : d153254 p = 0) : d155125 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153249 q = 0) : d155120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153249, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13793 q selected
    | true =>
      simp only [d153249, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13760 q selected
  have h2 (q : Pattern) (selected : d153250 q = 0) : d155121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153250, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153250, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153251 q = 0) : d155122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153251, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153251, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153065 q = 0) : d155002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153065, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13760 q selected
    | true =>
      simp only [d153065, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153066 q = 0) : d155003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153066, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153066, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153067 q = 0) : d155004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153067, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153067, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153252 q = 0) : d155123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153252, d155123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153252, d155123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153068 q = 0) : d155005 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153068, d155005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153068, d155005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153253 q = 0) : d155124 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153253, d155124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153253, d155124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153254 q = 0) : d155125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153254, d155125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153254, d155125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13795 (p : Pattern) (selected : d153260 p = 0) : d155131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153255 q = 0) : d155126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153255, d155126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13794 q selected
    | true =>
      simp only [d153255, d155126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153256 q = 0) : d155127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153256, d155127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153256, d155127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153071 q = 0) : d155008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153071, d155008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13761 q selected
    | true =>
      simp only [d153071, d155008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153072 q = 0) : d155009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153072, d155009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153072, d155009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153257 q = 0) : d155128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153257, d155128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153257, d155128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153258 q = 0) : d155129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153258, d155129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153258, d155129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153259 q = 0) : d155130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153259, d155130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153259, d155130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153260 q = 0) : d155131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153260, d155131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153260, d155131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13796 (p : Pattern) (selected : d153266 p = 0) : d155279 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153052 q = 0) : d155126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153052, d155126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13758 q selected
    | true =>
      simp only [d153052, d155126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153053 q = 0) : d155127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153053, d155127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153053, d155127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153263 q = 0) : d155276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153263, d155276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153263, d155276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153264 q = 0) : d155277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153264, d155277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153264, d155277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153265 q = 0) : d155278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153265, d155278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153265, d155278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153266 q = 0) : d155279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153266, d155279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153266, d155279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13797 (p : Pattern) (selected : d153272 p = 0) : d155285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153242 q = 0) : d155274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153242, d155274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13792 q selected
    | true =>
      simp only [d153242, d155274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13759 q selected
  have h2 (q : Pattern) (selected : d153261 q = 0) : d155132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153261, d155132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13795 q selected
    | true =>
      simp only [d153261, d155132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13762 q selected
  have h3 (q : Pattern) (selected : d153262 q = 0) : d155275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153262, d155275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153262, d155275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153267 q = 0) : d155280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153267, d155280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13796 q selected
    | true =>
      simp only [d153267, d155280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153268 q = 0) : d155281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153268, d155281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153268, d155281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153269 q = 0) : d155282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153269, d155282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153269, d155282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153270 q = 0) : d155283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153270, d155283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153270, d155283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153271 q = 0) : d155284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153271, d155284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153271, d155284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153272 q = 0) : d155285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153272, d155285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153272, d155285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13798 (p : Pattern) (selected : d153278 p = 0) : d155291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152917 q = 0) : d155014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152917, d155014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13734 q selected
    | true =>
      simp only [d152917, d155014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153274 q = 0) : d155287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153274, d155287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153274, d155287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153275 q = 0) : d155288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153275, d155288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153275, d155288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153276 q = 0) : d155289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153276, d155289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153276, d155289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153277 q = 0) : d155290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153277, d155290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153277, d155290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153278 q = 0) : d155291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153278, d155291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153278, d155291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13799 (p : Pattern) (selected : d153284 p = 0) : d155297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153100 q = 0) : d155155 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153100, d155155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153100, d155155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13766 q selected
  have h2 (q : Pattern) (selected : d153101 q = 0) : d155156 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153101, d155156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153101, d155156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153107 q = 0) : d155162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153107, d155162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13766 q selected
    | true =>
      simp only [d153107, d155162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13767 q selected
  have h4 (q : Pattern) (selected : d153108 q = 0) : d155163 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153108, d155163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153108, d155163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153109 q = 0) : d155164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153109, d155164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153109, d155164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153203 q = 0) : d155235 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153203, d155235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13780 q selected
    | true =>
      simp only [d153203, d155235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13786 q selected
  have h7 (q : Pattern) (selected : d153205 q = 0) : d155237 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153205, d155237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13787 q selected
    | true =>
      simp only [d153205, d155237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13738 q selected
  have h8 (q : Pattern) (selected : d153206 q = 0) : d155238 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153206, d155238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153206, d155238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153207 q = 0) : d155239 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153207, d155239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153207, d155239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d153208 q = 0) : d155240 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153208, d155240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153208, d155240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153212 q = 0) : d155244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153212, d155244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153212, d155244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13788 q selected
  have h12 (q : Pattern) (selected : d153214 q = 0) : d155246 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153214, d155246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153214, d155246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13789 q selected
  have h13 (q : Pattern) (selected : d153215 q = 0) : d155247 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153215, d155247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153215, d155247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153216 q = 0) : d155248 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153216, d155248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153216, d155248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153217 q = 0) : d155249 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153217, d155249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153217, d155249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153218 q = 0) : d155250 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153218, d155250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153218, d155250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153273 q = 0) : d155286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153273, d155286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153273, d155286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13797 q selected
  have h18 (q : Pattern) (selected : d153279 q = 0) : d155292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153279, d155292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153279, d155292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13798 q selected
  have h19 (q : Pattern) (selected : d153280 q = 0) : d155293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153280, d155293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d153280, d155293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d153281 q = 0) : d155294 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153281, d155294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153281, d155294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d153282 q = 0) : d155295 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153282, d155295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d153282, d155295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d153283 q = 0) : d155296 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153283, d155296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153283, d155296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d153284 q = 0) : d155297 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d153284, d155297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153284, d155297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro13800 (p : Pattern) (selected : d153290 p = 0) : d155303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153285 q = 0) : d155298 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d153285, d155298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153285, d155298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13799 q selected
  have h2 (q : Pattern) (selected : d153286 q = 0) : d155299 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d153286, d155299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153286, d155299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153287 q = 0) : d155300 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d153287, d155300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153287, d155300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153288 q = 0) : d155301 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d153288, d155301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153288, d155301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153289 q = 0) : d155302 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d153289, d155302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153289, d155302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153290 q = 0) : d155303 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d153290, d155303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153290, d155303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13801 (p : Pattern) (selected : d153294 p = 0) : d155307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153137 q = 0) : d155192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153137, d155192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13772 q selected
    | true =>
      simp only [d153137, d155192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13742 q selected
  have h2 (q : Pattern) (selected : d153138 q = 0) : d155193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153138, d155193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153138, d155193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153139 q = 0) : d155194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153139, d155194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153139, d155194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152969 q = 0) : d155066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13742 q selected
    | true =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13725 q selected
  have h5 (q : Pattern) (selected : d152970 q = 0) : d155067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152971 q = 0) : d155068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153140 q = 0) : d155195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153140, d155195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153140, d155195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153292 q = 0) : d155305 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153292, d155305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153292, d155305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153293 q = 0) : d155306 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153293, d155306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153293, d155306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153294 q = 0) : d155307 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153294, d155307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153294, d155307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13802 (p : Pattern) (selected : d153298 p = 0) : d155311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152969 q = 0) : d155066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13742 q selected
    | true =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13725 q selected
  have h2 (q : Pattern) (selected : d152970 q = 0) : d155067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152971 q = 0) : d155068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153292 q = 0) : d155305 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153292, d155305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153292, d155305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153297 q = 0) : d155310 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153297, d155310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153297, d155310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153298 q = 0) : d155311 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153298, d155311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153298, d155311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13803 (p : Pattern) (selected : d153304 p = 0) : d155317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153295 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13801 q selected
    | true =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153296 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153301 q = 0) : d155314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153302 q = 0) : d155315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153302, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153302, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153303 q = 0) : d155316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153303, d155316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153303, d155316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153304 q = 0) : d155317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153304, d155317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153304, d155317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13804 (p : Pattern) (selected : d153308 p = 0) : d155321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153305 q = 0) : d155318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153306 q = 0) : d155319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153306, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153306, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153307 q = 0) : d155320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153307, d155320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153307, d155320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153308 q = 0) : d155321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153308, d155321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153308, d155321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13805 (p : Pattern) (selected : d153314 p = 0) : d155327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153309 q = 0) : d155322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153309, d155322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13803 q selected
    | true =>
      simp only [d153309, d155322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13804 q selected
  have h2 (q : Pattern) (selected : d153310 q = 0) : d155323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153310, d155323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153310, d155323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153311 q = 0) : d155324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153311, d155324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153311, d155324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153312 q = 0) : d155325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153312, d155325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153312, d155325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153313 q = 0) : d155326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153313, d155326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153313, d155326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153314 q = 0) : d155327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153314, d155327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153314, d155327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13806 (p : Pattern) (selected : d153317 p = 0) : d155330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153295 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13801 q selected
    | true =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153296 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153301 q = 0) : d155314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153302 q = 0) : d155315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153302, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153302, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153303 q = 0) : d155316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153303, d155316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153303, d155316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153317 q = 0) : d155330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153317, d155330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153317, d155330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13807 (p : Pattern) (selected : d153318 p = 0) : d155331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153305 q = 0) : d155318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153306 q = 0) : d155319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153306, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153306, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153307 q = 0) : d155320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153307, d155320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153307, d155320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153318 q = 0) : d155331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153318, d155331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153318, d155331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13808 (p : Pattern) (selected : d153324 p = 0) : d155337 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153309 q = 0) : d155322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153309, d155322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13803 q selected
    | true =>
      simp only [d153309, d155322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13804 q selected
  have h2 (q : Pattern) (selected : d153310 q = 0) : d155323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153310, d155323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153310, d155323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153311 q = 0) : d155324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153311, d155324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153311, d155324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153312 q = 0) : d155325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153312, d155325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153312, d155325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153313 q = 0) : d155326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153313, d155326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153313, d155326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153319 q = 0) : d155332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153319, d155332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13806 q selected
    | true =>
      simp only [d153319, d155332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13807 q selected
  have h7 (q : Pattern) (selected : d153320 q = 0) : d155333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153320, d155333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153320, d155333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153321 q = 0) : d155334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153321, d155334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153321, d155334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153322 q = 0) : d155335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153322, d155335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153322, d155335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153323 q = 0) : d155336 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153323, d155336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153323, d155336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153324 q = 0) : d155337 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153324, d155337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153324, d155337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13809 (p : Pattern) (selected : d153329 p = 0) : d155342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153295 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13801 q selected
    | true =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153296 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153301 q = 0) : d155314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153302 q = 0) : d155315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153302, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153302, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153328 q = 0) : d155341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153328, d155341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153328, d155341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153329 q = 0) : d155342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153329, d155342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153329, d155342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13810 (p : Pattern) (selected : d153331 p = 0) : d155344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153305 q = 0) : d155318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153306 q = 0) : d155319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153306, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153306, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153330 q = 0) : d155343 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153330, d155343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153330, d155343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153331 q = 0) : d155344 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153331, d155344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153331, d155344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13811 (p : Pattern) (selected : d153338 p = 0) : d155351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153295 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13801 q selected
    | true =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153296 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153301 q = 0) : d155314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153336 q = 0) : d155349 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153336, d155349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153336, d155349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153337 q = 0) : d155350 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153337, d155350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153337, d155350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153338 q = 0) : d155351 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153338, d155351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153338, d155351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13812 (p : Pattern) (selected : d153341 p = 0) : d155354 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153305 q = 0) : d155318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153339 q = 0) : d155352 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153339, d155352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153339, d155352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153340 q = 0) : d155353 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153340, d155353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153340, d155353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153341 q = 0) : d155354 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153341, d155354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153341, d155354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13813 (p : Pattern) (selected : d153346 p = 0) : d155359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d531 q = 0) : d52278 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d532 q = 0) : d52279 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d537 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro276 q selected
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d538 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153345 q = 0) : d155358 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153345, d155358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153345, d155358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153346 q = 0) : d155359 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153346, d155359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153346, d155359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13814 (p : Pattern) (selected : d153353 p = 0) : d155366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9581 q = 0) : d101161 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6640 q selected
    | true =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9582 q = 0) : d101162 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153352 q = 0) : d155365 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153352, d155365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153352, d155365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153353 q = 0) : d155366 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153353, d155366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153353, d155366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro13815 (p : Pattern) (selected : d153359 p = 0) : d155372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153347 q = 0) : d155360 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153347, d155360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13813 q selected
    | true =>
      simp only [d153347, d155360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153348 q = 0) : d155361 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153348, d155361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153348, d155361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153349 q = 0) : d155362 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153349, d155362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153349, d155362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153350 q = 0) : d155363 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153350, d155363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153350, d155363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153124 q = 0) : d155179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153124, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13770 q selected
    | true =>
      simp only [d153124, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153125 q = 0) : d155180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153125, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153125, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153126 q = 0) : d155181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153126, d155181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153126, d155181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153127 q = 0) : d155182 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153127, d155182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153127, d155182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153351 q = 0) : d155364 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153351, d155364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153351, d155364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153354 q = 0) : d155367 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13814 q selected
    | true =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153355 q = 0) : d155368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153356 q = 0) : d155369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153356, d155369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153356, d155369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153357 q = 0) : d155370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153357, d155370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153357, d155370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153133 q = 0) : d155188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153134 q = 0) : d155189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153358 q = 0) : d155371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153358, d155371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153358, d155371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153359 q = 0) : d155372 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153359, d155372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153359, d155372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro13816 (p : Pattern) (selected : d153363 p = 0) : d155376 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153133 q = 0) : d155188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153134 q = 0) : d155189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152858 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
    | true =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152859 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152860 q = 0) : d154957 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152860, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152860, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152861 q = 0) : d154958 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152861, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152861, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153135 q = 0) : d155190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153135, d155190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153135, d155190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152862 q = 0) : d154959 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152862, d154959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d152862, d154959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153363 q = 0) : d155376 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153363, d155376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153363, d155376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13817 (p : Pattern) (selected : d153369 p = 0) : d155382 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153360 q = 0) : d155373 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153360, d155373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13815 q selected
    | true =>
      simp only [d153360, d155373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13772 q selected
  have h2 (q : Pattern) (selected : d153361 q = 0) : d155374 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153361, d155374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153361, d155374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153362 q = 0) : d155375 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153362, d155375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153362, d155375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153364 q = 0) : d155377 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153364, d155377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13772 q selected
    | true =>
      simp only [d153364, d155377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13816 q selected
  have h5 (q : Pattern) (selected : d153365 q = 0) : d155378 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153365, d155378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153365, d155378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153366 q = 0) : d155379 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153366, d155379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153366, d155379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153367 q = 0) : d155380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153367, d155380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153367, d155380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153137 q = 0) : d155192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153137, d155192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13772 q selected
    | true =>
      simp only [d153137, d155192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13742 q selected
  have h9 (q : Pattern) (selected : d153138 q = 0) : d155193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153138, d155193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153138, d155193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153139 q = 0) : d155194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153139, d155194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153139, d155194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d152969 q = 0) : d155066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13742 q selected
    | true =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13725 q selected
  have h12 (q : Pattern) (selected : d152970 q = 0) : d155067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d152971 q = 0) : d155068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153140 q = 0) : d155195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153140, d155195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153140, d155195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153368 q = 0) : d155381 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153368, d155381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153368, d155381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153369 q = 0) : d155382 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153369, d155382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153369, d155382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13818 (p : Pattern) (selected : d153375 p = 0) : d155388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153370 q = 0) : d155383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153370, d155383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13817 q selected
    | true =>
      simp only [d153370, d155383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153371 q = 0) : d155384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153371, d155384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153371, d155384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153295 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13801 q selected
    | true =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153296 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153372 q = 0) : d155385 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153372, d155385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153372, d155385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153373 q = 0) : d155386 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153373, d155386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153373, d155386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153374 q = 0) : d155387 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153374, d155387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153374, d155387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153375 q = 0) : d155388 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153375, d155388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153375, d155388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13819 (p : Pattern) (selected : d153378 p = 0) : d155178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d568 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d568, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d568, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d569 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d569, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d569, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d344 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153377 q = 0) : d155177 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153377, d155177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153377, d155177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153378 q = 0) : d155178 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153378, d155178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153378, d155178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13820 (p : Pattern) (selected : d153385 p = 0) : d155185 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9655 q = 0) : d101067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9655, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6653 q selected
    | true =>
      simp only [d9655, d101067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9656 q = 0) : d101068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9656, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9656, d101068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153384 q = 0) : d155184 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153384, d155184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153384, d155184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153385 q = 0) : d155185 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153385, d155185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153385, d155185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro13821 (p : Pattern) (selected : d153391 p = 0) : d155191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153379 q = 0) : d155179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153379, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13819 q selected
    | true =>
      simp only [d153379, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153380 q = 0) : d155180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153380, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153380, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153381 q = 0) : d155181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153381, d155181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153381, d155181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153382 q = 0) : d155182 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153382, d155182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153382, d155182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153152 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13775 q selected
    | true =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153153 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153154 q = 0) : d155062 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153154, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153154, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153155 q = 0) : d155063 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153155, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153155, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153383 q = 0) : d155183 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153383, d155183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153383, d155183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153386 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13820 q selected
    | true =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153387 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153388 q = 0) : d155188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153388, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153388, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153389 q = 0) : d155189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153389, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153389, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d152984 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13745 q selected
    | true =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d152985 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d152986 q = 0) : d154957 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152986, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152986, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d152987 q = 0) : d154958 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152987, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d152987, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153390 q = 0) : d155190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153390, d155190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153390, d155190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153391 q = 0) : d155191 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153391, d155191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153391, d155191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro13822 (p : Pattern) (selected : d153398 p = 0) : d155307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153392 q = 0) : d155192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153392, d155192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13821 q selected
    | true =>
      simp only [d153392, d155192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13776 q selected
  have h2 (q : Pattern) (selected : d153393 q = 0) : d155193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153393, d155193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153393, d155193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153394 q = 0) : d155194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153394, d155194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153394, d155194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153158 q = 0) : d155066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153158, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13776 q selected
    | true =>
      simp only [d153158, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13746 q selected
  have h5 (q : Pattern) (selected : d153159 q = 0) : d155067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153159, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153159, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153160 q = 0) : d155068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153160, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153160, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153395 q = 0) : d155195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153395, d155195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153395, d155195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153396 q = 0) : d155305 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153396, d155305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153396, d155305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153397 q = 0) : d155306 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153397, d155306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153397, d155306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153398 q = 0) : d155307 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153398, d155307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153398, d155307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13823 (p : Pattern) (selected : d153402 p = 0) : d155311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153158 q = 0) : d155066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153158, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13776 q selected
    | true =>
      simp only [d153158, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13746 q selected
  have h2 (q : Pattern) (selected : d153159 q = 0) : d155067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153159, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153159, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153160 q = 0) : d155068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153160, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153160, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153396 q = 0) : d155305 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153396, d155305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153396, d155305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153401 q = 0) : d155310 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153401, d155310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153401, d155310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153402 q = 0) : d155311 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153402, d155311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153402, d155311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13824 (p : Pattern) (selected : d153408 p = 0) : d155317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153399 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153399, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13822 q selected
    | true =>
      simp only [d153399, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153400 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153400, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153400, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153403 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153403, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13823 q selected
    | true =>
      simp only [d153403, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153404 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153404, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153404, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153405 q = 0) : d155314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153405, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153405, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153406 q = 0) : d155315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153406, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153406, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153407 q = 0) : d155316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153407, d155316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153407, d155316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153408 q = 0) : d155317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153408, d155317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153408, d155317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13825 (p : Pattern) (selected : d153412 p = 0) : d155321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153403 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153403, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13823 q selected
    | true =>
      simp only [d153403, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153404 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153404, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153404, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153409 q = 0) : d155318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153409, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153409, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153410 q = 0) : d155319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153410, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153410, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153411 q = 0) : d155320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153411, d155320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153411, d155320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153412 q = 0) : d155321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153412, d155321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153412, d155321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13826 (p : Pattern) (selected : d153418 p = 0) : d155394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153295 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13801 q selected
    | true =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153296 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153415 q = 0) : d155391 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153415, d155391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153415, d155391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153416 q = 0) : d155392 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153416, d155392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153416, d155392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153417 q = 0) : d155393 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153417, d155393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153417, d155393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153418 q = 0) : d155394 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153418, d155394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153418, d155394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13827 (p : Pattern) (selected : d153424 p = 0) : d155400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153332 q = 0) : d155345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153332, d155345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13809 q selected
    | true =>
      simp only [d153332, d155345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13810 q selected
  have h2 (q : Pattern) (selected : d153333 q = 0) : d155346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153333, d155346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153333, d155346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153334 q = 0) : d155347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153334, d155347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153334, d155347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153335 q = 0) : d155348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153335, d155348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153335, d155348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153342 q = 0) : d155355 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153342, d155355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13811 q selected
    | true =>
      simp only [d153342, d155355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13812 q selected
  have h6 (q : Pattern) (selected : d153343 q = 0) : d155356 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153343, d155356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153343, d155356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153344 q = 0) : d155357 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153344, d155357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153344, d155357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153376 q = 0) : d155389 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153376, d155389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13818 q selected
    | true =>
      simp only [d153376, d155389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13803 q selected
  have h9 (q : Pattern) (selected : d153413 q = 0) : d155322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153413, d155322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13824 q selected
    | true =>
      simp only [d153413, d155322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13825 q selected
  have h10 (q : Pattern) (selected : d153414 q = 0) : d155390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153414, d155390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153414, d155390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153419 q = 0) : d155395 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153419, d155395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13826 q selected
    | true =>
      simp only [d153419, d155395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153420 q = 0) : d155396 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153420, d155396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153420, d155396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153421 q = 0) : d155397 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153421, d155397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153421, d155397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153422 q = 0) : d155398 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153422, d155398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153422, d155398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153423 q = 0) : d155399 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153423, d155399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153423, d155399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153424 q = 0) : d155400 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153424, d155400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153424, d155400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro13828 (p : Pattern) (selected : d153425 p = 0) : d155401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153295 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13801 q selected
    | true =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153296 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153301 q = 0) : d155314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153302 q = 0) : d155315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153302, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153302, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153328 q = 0) : d155341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153328, d155341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153328, d155341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153425 q = 0) : d155401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153425, d155401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153425, d155401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13829 (p : Pattern) (selected : d153426 p = 0) : d155402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153305 q = 0) : d155318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153306 q = 0) : d155319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153306, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153306, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153330 q = 0) : d155343 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153330, d155343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153330, d155343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153426 q = 0) : d155402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153426, d155402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153426, d155402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13830 (p : Pattern) (selected : d153431 p = 0) : d155407 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153295 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13801 q selected
    | true =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153296 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153301 q = 0) : d155314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153301, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153336 q = 0) : d155349 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153336, d155349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153336, d155349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153337 q = 0) : d155350 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153337, d155350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153337, d155350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153431 q = 0) : d155407 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153431, d155407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153431, d155407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13831 (p : Pattern) (selected : d153432 p = 0) : d155408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153299 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13802 q selected
    | true =>
      simp only [d153299, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153300 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153300, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153305 q = 0) : d155318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153305, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153339 q = 0) : d155352 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153339, d155352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153339, d155352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153340 q = 0) : d155353 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153340, d155353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153340, d155353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153432 q = 0) : d155408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153432, d155408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153432, d155408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13832 (p : Pattern) (selected : d153436 p = 0) : d155412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153370 q = 0) : d155383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153370, d155383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13817 q selected
    | true =>
      simp only [d153370, d155383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153371 q = 0) : d155384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153371, d155384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153371, d155384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153295 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13801 q selected
    | true =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153296 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153372 q = 0) : d155385 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153372, d155385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153372, d155385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153373 q = 0) : d155386 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153373, d155386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153373, d155386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153374 q = 0) : d155387 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153374, d155387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153374, d155387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153436 q = 0) : d155412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153436, d155412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153436, d155412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13833 (p : Pattern) (selected : d153438 p = 0) : d155330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153399 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153399, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13822 q selected
    | true =>
      simp only [d153399, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153400 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153400, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153400, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153403 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153403, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13823 q selected
    | true =>
      simp only [d153403, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153404 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153404, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153404, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153405 q = 0) : d155314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153405, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153405, d155314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153406 q = 0) : d155315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153406, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153406, d155315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153407 q = 0) : d155316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153407, d155316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153407, d155316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153438 q = 0) : d155330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153438, d155330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153438, d155330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13834 (p : Pattern) (selected : d153439 p = 0) : d155331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153403 q = 0) : d155312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153403, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13823 q selected
    | true =>
      simp only [d153403, d155312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153404 q = 0) : d155313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153404, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153404, d155313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153409 q = 0) : d155318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153409, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153409, d155318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153410 q = 0) : d155319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153410, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153410, d155319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153411 q = 0) : d155320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153411, d155320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153411, d155320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153439 q = 0) : d155331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153439, d155331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153439, d155331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13835 (p : Pattern) (selected : d153442 p = 0) : d155415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153295 q = 0) : d155308 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13801 q selected
    | true =>
      simp only [d153295, d155308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153296 q = 0) : d155309 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153296, d155309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153415 q = 0) : d155391 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153415, d155391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153415, d155391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153416 q = 0) : d155392 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153416, d155392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153416, d155392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153417 q = 0) : d155393 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153417, d155393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153417, d155393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153442 q = 0) : d155415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153442, d155415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153442, d155415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13836 (p : Pattern) (selected : d153448 p = 0) : d155421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153332 q = 0) : d155345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153332, d155345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13809 q selected
    | true =>
      simp only [d153332, d155345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13810 q selected
  have h2 (q : Pattern) (selected : d153333 q = 0) : d155346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153333, d155346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153333, d155346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153334 q = 0) : d155347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153334, d155347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153334, d155347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153335 q = 0) : d155348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153335, d155348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153335, d155348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153342 q = 0) : d155355 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153342, d155355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13811 q selected
    | true =>
      simp only [d153342, d155355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13812 q selected
  have h6 (q : Pattern) (selected : d153343 q = 0) : d155356 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153343, d155356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153343, d155356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153344 q = 0) : d155357 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153344, d155357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153344, d155357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153376 q = 0) : d155389 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153376, d155389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13818 q selected
    | true =>
      simp only [d153376, d155389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13803 q selected
  have h9 (q : Pattern) (selected : d153413 q = 0) : d155322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153413, d155322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13824 q selected
    | true =>
      simp only [d153413, d155322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13825 q selected
  have h10 (q : Pattern) (selected : d153414 q = 0) : d155390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153414, d155390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153414, d155390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153419 q = 0) : d155395 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153419, d155395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13826 q selected
    | true =>
      simp only [d153419, d155395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153420 q = 0) : d155396 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153420, d155396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153420, d155396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153421 q = 0) : d155397 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153421, d155397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153421, d155397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153422 q = 0) : d155398 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153422, d155398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153422, d155398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153423 q = 0) : d155399 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153423, d155399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153423, d155399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153427 q = 0) : d155403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153427, d155403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13828 q selected
    | true =>
      simp only [d153427, d155403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13829 q selected
  have h17 (q : Pattern) (selected : d153428 q = 0) : d155404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153428, d155404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153428, d155404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d153429 q = 0) : d155405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153429, d155405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d153429, d155405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d153430 q = 0) : d155406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153430, d155406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153430, d155406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d153433 q = 0) : d155409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153433, d155409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13830 q selected
    | true =>
      simp only [d153433, d155409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13831 q selected
  have h21 (q : Pattern) (selected : d153434 q = 0) : d155410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153434, d155410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153434, d155410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d153435 q = 0) : d155411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153435, d155411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153435, d155411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d153437 q = 0) : d155413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153437, d155413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13832 q selected
    | true =>
      simp only [d153437, d155413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13806 q selected
  have h24 (q : Pattern) (selected : d153440 q = 0) : d155332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153440, d155332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13833 q selected
    | true =>
      simp only [d153440, d155332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13834 q selected
  have h25 (q : Pattern) (selected : d153441 q = 0) : d155414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153441, d155414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d153441, d155414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d153443 q = 0) : d155416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153443, d155416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13835 q selected
    | true =>
      simp only [d153443, d155416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d153444 q = 0) : d155417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153444, d155417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d153444, d155417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d153445 q = 0) : d155418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153445, d155418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d153445, d155418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d153446 q = 0) : d155419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153446, d155419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d153446, d155419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d153447 q = 0) : d155420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153447, d155420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153447, d155420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d153448 q = 0) : d155421 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153448, d155421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153448, d155421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro13837 (p : Pattern) (selected : d153455 p = 0) : d155428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153309 q = 0) : d155322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153309, d155322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13803 q selected
    | true =>
      simp only [d153309, d155322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13804 q selected
  have h2 (q : Pattern) (selected : d153310 q = 0) : d155323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153310, d155323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153310, d155323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153311 q = 0) : d155324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153311, d155324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153311, d155324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153312 q = 0) : d155325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153312, d155325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153312, d155325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153313 q = 0) : d155326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153313, d155326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153313, d155326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153450 q = 0) : d155423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153450, d155423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13804 q selected
    | true =>
      simp only [d153450, d155423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153451 q = 0) : d155424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153451, d155424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153451, d155424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153452 q = 0) : d155425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153452, d155425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153452, d155425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153453 q = 0) : d155426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153453, d155426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153453, d155426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153454 q = 0) : d155427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153454, d155427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153454, d155427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153455 q = 0) : d155428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153455, d155428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153455, d155428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13838 (p : Pattern) (selected : d153461 p = 0) : d155434 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153450 q = 0) : d155423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153450, d155423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13804 q selected
    | true =>
      simp only [d153450, d155423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153451 q = 0) : d155424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153451, d155424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153451, d155424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153452 q = 0) : d155425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153452, d155425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153452, d155425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153453 q = 0) : d155426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153453, d155426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153453, d155426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153454 q = 0) : d155427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153454, d155427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153454, d155427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153456 q = 0) : d155429 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153456, d155429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13807 q selected
    | true =>
      simp only [d153456, d155429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153457 q = 0) : d155430 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153457, d155430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153457, d155430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153458 q = 0) : d155431 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153458, d155431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153458, d155431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153459 q = 0) : d155432 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153459, d155432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153459, d155432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153460 q = 0) : d155433 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153460, d155433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153460, d155433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153461 q = 0) : d155434 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153461, d155434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153461, d155434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13839 (p : Pattern) (selected : d153468 p = 0) : d155441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153437 q = 0) : d155413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153437, d155413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13832 q selected
    | true =>
      simp only [d153437, d155413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13806 q selected
  have h2 (q : Pattern) (selected : d153440 q = 0) : d155332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153440, d155332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13833 q selected
    | true =>
      simp only [d153440, d155332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13834 q selected
  have h3 (q : Pattern) (selected : d153441 q = 0) : d155414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153441, d155414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153441, d155414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153443 q = 0) : d155416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153443, d155416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13835 q selected
    | true =>
      simp only [d153443, d155416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153444 q = 0) : d155417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153444, d155417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153444, d155417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153445 q = 0) : d155418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153445, d155418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153445, d155418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153466 q = 0) : d155439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153466, d155439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153466, d155439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153467 q = 0) : d155440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153467, d155440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153467, d155440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153468 q = 0) : d155441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153468, d155441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153468, d155441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13840 (p : Pattern) (selected : d153470 p = 0) : d155443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153456 q = 0) : d155429 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153456, d155429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13807 q selected
    | true =>
      simp only [d153456, d155429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153457 q = 0) : d155430 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153457, d155430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153457, d155430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153458 q = 0) : d155431 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153458, d155431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153458, d155431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153459 q = 0) : d155432 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153459, d155432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153459, d155432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153460 q = 0) : d155433 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153460, d155433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153460, d155433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153470 q = 0) : d155443 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153470, d155443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153470, d155443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13841 (p : Pattern) (selected : d153486 p = 0) : d155459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153476 q = 0) : d155449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153476, d155449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153476, d155449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13813 q selected
  have h2 (q : Pattern) (selected : d153347 q = 0) : d155360 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153347, d155360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13813 q selected
    | true =>
      simp only [d153347, d155360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153477 q = 0) : d155450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153477, d155450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153477, d155450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153348 q = 0) : d155361 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153348, d155361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153348, d155361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153478 q = 0) : d155451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153478, d155451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153478, d155451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153479 q = 0) : d155452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153479, d155452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153479, d155452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153219 q = 0) : d155251 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153219, d155251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153219, d155251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13770 q selected
  have h8 (q : Pattern) (selected : d153124 q = 0) : d155179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153124, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13770 q selected
    | true =>
      simp only [d153124, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153220 q = 0) : d155252 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153220, d155252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153220, d155252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153125 q = 0) : d155180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153125, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153125, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153221 q = 0) : d155253 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153221, d155253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153221, d155253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153222 q = 0) : d155254 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153222, d155254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153222, d155254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153480 q = 0) : d155453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153480, d155453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153480, d155453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153481 q = 0) : d155454 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153481, d155454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153481, d155454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13814 q selected
  have h15 (q : Pattern) (selected : d153354 q = 0) : d155367 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13814 q selected
    | true =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153482 q = 0) : d155455 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153482, d155455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153482, d155455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153355 q = 0) : d155368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153483 q = 0) : d155456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153483, d155456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153483, d155456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153484 q = 0) : d155457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153484, d155457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153484, d155457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153224 q = 0) : d155256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
  have h21 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d153225 q = 0) : d155257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d153226 q = 0) : d155258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d153227 q = 0) : d155259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d153485 q = 0) : d155458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153485, d155458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153485, d155458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d153486 q = 0) : d155459 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153486, d155459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153486, d155459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro13842 (p : Pattern) (selected : d153490 p = 0) : d155463 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153224 q = 0) : d155256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
  have h2 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153225 q = 0) : d155257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153226 q = 0) : d155258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153227 q = 0) : d155259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152899 q = 0) : d154996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152899, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152899, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
  have h8 (q : Pattern) (selected : d152858 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
    | true =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152900 q = 0) : d154997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152900, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152900, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152859 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d152901 q = 0) : d154998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152901, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d152901, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d152902 q = 0) : d154999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152902, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d152902, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153228 q = 0) : d155260 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153228, d155260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153228, d155260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d152903 q = 0) : d155000 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152903, d155000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d152903, d155000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153490 q = 0) : d155463 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153490, d155463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153490, d155463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13843 (p : Pattern) (selected : d153496 p = 0) : d155469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153487 q = 0) : d155460 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153487, d155460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13841 q selected
    | true =>
      simp only [d153487, d155460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13790 q selected
  have h2 (q : Pattern) (selected : d153488 q = 0) : d155461 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153488, d155461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153488, d155461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153489 q = 0) : d155462 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153489, d155462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153489, d155462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153491 q = 0) : d155464 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153491, d155464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13790 q selected
    | true =>
      simp only [d153491, d155464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13842 q selected
  have h5 (q : Pattern) (selected : d153492 q = 0) : d155465 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153492, d155465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153492, d155465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153493 q = 0) : d155466 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153493, d155466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153493, d155466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153494 q = 0) : d155467 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153494, d155467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153494, d155467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153230 q = 0) : d155262 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153230, d155262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13790 q selected
    | true =>
      simp only [d153230, d155262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13757 q selected
  have h9 (q : Pattern) (selected : d153231 q = 0) : d155263 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153231, d155263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153231, d155263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153232 q = 0) : d155264 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153232, d155264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153232, d155264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153046 q = 0) : d155120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13757 q selected
    | true =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13732 q selected
  have h12 (q : Pattern) (selected : d153047 q = 0) : d155121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153048 q = 0) : d155122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153233 q = 0) : d155265 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153233, d155265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153233, d155265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153495 q = 0) : d155468 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153495, d155468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153495, d155468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153496 q = 0) : d155469 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153496, d155469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153496, d155469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13844 (p : Pattern) (selected : d153501 p = 0) : d155474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153230 q = 0) : d155262 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153230, d155262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13790 q selected
    | true =>
      simp only [d153230, d155262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13757 q selected
  have h2 (q : Pattern) (selected : d153231 q = 0) : d155263 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153231, d155263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153231, d155263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153232 q = 0) : d155264 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153232, d155264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153232, d155264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153046 q = 0) : d155120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13757 q selected
    | true =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13732 q selected
  have h5 (q : Pattern) (selected : d153047 q = 0) : d155121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153048 q = 0) : d155122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153233 q = 0) : d155265 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153233, d155265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153233, d155265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153499 q = 0) : d155472 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153499, d155472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153499, d155472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153500 q = 0) : d155473 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153500, d155473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153500, d155473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153501 q = 0) : d155474 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153501, d155474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153501, d155474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13845 (p : Pattern) (selected : d153507 p = 0) : d155480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153497 q = 0) : d155470 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153497, d155470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13843 q selected
    | true =>
      simp only [d153497, d155470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153498 q = 0) : d155471 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153498, d155471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153498, d155471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153502 q = 0) : d155475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153502, d155475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13844 q selected
    | true =>
      simp only [d153502, d155475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153503 q = 0) : d155476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153503, d155476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153503, d155476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153504 q = 0) : d155477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153504, d155477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153504, d155477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153505 q = 0) : d155478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153505, d155478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153505, d155478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153506 q = 0) : d155479 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153506, d155479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153506, d155479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153507 q = 0) : d155480 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153507, d155480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153507, d155480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13846 (p : Pattern) (selected : d153509 p = 0) : d155482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153046 q = 0) : d155120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13757 q selected
    | true =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13732 q selected
  have h2 (q : Pattern) (selected : d153047 q = 0) : d155121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153048 q = 0) : d155122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153499 q = 0) : d155472 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153499, d155472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153499, d155472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153508 q = 0) : d155481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153508, d155481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153508, d155481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153509 q = 0) : d155482 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153509, d155482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153509, d155482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13847 (p : Pattern) (selected : d153515 p = 0) : d155488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153502 q = 0) : d155475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153502, d155475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13844 q selected
    | true =>
      simp only [d153502, d155475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153503 q = 0) : d155476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153503, d155476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153503, d155476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153510 q = 0) : d155483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153510, d155483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13846 q selected
    | true =>
      simp only [d153510, d155483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153511 q = 0) : d155484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153511, d155484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153511, d155484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153512 q = 0) : d155485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153512, d155485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153512, d155485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153513 q = 0) : d155486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153513, d155486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153513, d155486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153514 q = 0) : d155487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153514, d155487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153514, d155487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153515 q = 0) : d155488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153515, d155488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153515, d155488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13848 (p : Pattern) (selected : d153527 p = 0) : d155261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153517 q = 0) : d155251 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153517, d155251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153517, d155251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13819 q selected
  have h2 (q : Pattern) (selected : d153379 q = 0) : d155179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153379, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13819 q selected
    | true =>
      simp only [d153379, d155179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153518 q = 0) : d155252 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153518, d155252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153518, d155252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153380 q = 0) : d155180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153380, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153380, d155180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153519 q = 0) : d155253 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153519, d155253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153519, d155253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153520 q = 0) : d155254 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153520, d155254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153520, d155254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153243 q = 0) : d155114 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153243, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153243, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13775 q selected
  have h8 (q : Pattern) (selected : d153152 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13775 q selected
    | true =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153244 q = 0) : d155115 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153244, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153244, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153153 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153245 q = 0) : d155116 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153245, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153245, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153246 q = 0) : d155117 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153246, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153246, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153521 q = 0) : d155255 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153521, d155255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153521, d155255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153522 q = 0) : d155256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153522, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153522, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13820 q selected
  have h15 (q : Pattern) (selected : d153386 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13820 q selected
    | true =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153523 q = 0) : d155257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153523, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153523, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153387 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153524 q = 0) : d155258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153524, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153524, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153525 q = 0) : d155259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153525, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153525, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153059 q = 0) : d154996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153059, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153059, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13745 q selected
  have h21 (q : Pattern) (selected : d152984 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13745 q selected
    | true =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d153060 q = 0) : d154997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153060, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d153060, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d152985 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d153061 q = 0) : d154998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153061, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d153061, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d153062 q = 0) : d154999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153062, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d153062, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d153526 q = 0) : d155260 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153526, d155260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153526, d155260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d153527 q = 0) : d155261 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153527, d155261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153527, d155261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro13849 (p : Pattern) (selected : d153534 p = 0) : d155474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153528 q = 0) : d155262 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153528, d155262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13848 q selected
    | true =>
      simp only [d153528, d155262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13793 q selected
  have h2 (q : Pattern) (selected : d153529 q = 0) : d155263 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153529, d155263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153529, d155263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153530 q = 0) : d155264 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153530, d155264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153530, d155264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153249 q = 0) : d155120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153249, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13793 q selected
    | true =>
      simp only [d153249, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13760 q selected
  have h5 (q : Pattern) (selected : d153250 q = 0) : d155121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153250, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153250, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153251 q = 0) : d155122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153251, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153251, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153531 q = 0) : d155265 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153531, d155265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153531, d155265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153532 q = 0) : d155472 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153532, d155472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153532, d155472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153533 q = 0) : d155473 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153533, d155473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153533, d155473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153534 q = 0) : d155474 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153534, d155474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153534, d155474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13850 (p : Pattern) (selected : d153538 p = 0) : d155482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153249 q = 0) : d155120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153249, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13793 q selected
    | true =>
      simp only [d153249, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13760 q selected
  have h2 (q : Pattern) (selected : d153250 q = 0) : d155121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153250, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153250, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153251 q = 0) : d155122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153251, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153251, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153532 q = 0) : d155472 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153532, d155472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153532, d155472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153537 q = 0) : d155481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153537, d155481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153537, d155481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153538 q = 0) : d155482 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153538, d155482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153538, d155482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13851 (p : Pattern) (selected : d153544 p = 0) : d155488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153535 q = 0) : d155475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153535, d155475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13849 q selected
    | true =>
      simp only [d153535, d155475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153536 q = 0) : d155476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153536, d155476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153536, d155476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153539 q = 0) : d155483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153539, d155483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13850 q selected
    | true =>
      simp only [d153539, d155483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153540 q = 0) : d155484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153540, d155484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153540, d155484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153541 q = 0) : d155485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153541, d155485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153541, d155485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153542 q = 0) : d155486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153542, d155486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153542, d155486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153543 q = 0) : d155487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153543, d155487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153543, d155487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153544 q = 0) : d155488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153544, d155488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153544, d155488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13852 (p : Pattern) (selected : d153548 p = 0) : d155493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153539 q = 0) : d155483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153539, d155483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13850 q selected
    | true =>
      simp only [d153539, d155483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153540 q = 0) : d155484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153540, d155484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153540, d155484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153545 q = 0) : d155490 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153545, d155490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153545, d155490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153546 q = 0) : d155491 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153546, d155491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153546, d155491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153547 q = 0) : d155492 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153547, d155492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153547, d155492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153548 q = 0) : d155493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153548, d155493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153548, d155493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13853 (p : Pattern) (selected : d153554 p = 0) : d155499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153502 q = 0) : d155475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153502, d155475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13844 q selected
    | true =>
      simp only [d153502, d155475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153503 q = 0) : d155476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153503, d155476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153503, d155476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153551 q = 0) : d155496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153551, d155496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153551, d155496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153552 q = 0) : d155497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153552, d155497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153552, d155497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153553 q = 0) : d155498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153553, d155498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153553, d155498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153554 q = 0) : d155499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153554, d155499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153554, d155499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13854 (p : Pattern) (selected : d153560 p = 0) : d155505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153516 q = 0) : d155489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153516, d155489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13845 q selected
    | true =>
      simp only [d153516, d155489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13847 q selected
  have h2 (q : Pattern) (selected : d153549 q = 0) : d155494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153549, d155494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13851 q selected
    | true =>
      simp only [d153549, d155494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13852 q selected
  have h3 (q : Pattern) (selected : d153550 q = 0) : d155495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153550, d155495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153550, d155495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153555 q = 0) : d155500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153555, d155500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13853 q selected
    | true =>
      simp only [d153555, d155500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153556 q = 0) : d155501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153556, d155501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153556, d155501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153557 q = 0) : d155502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153557, d155502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153557, d155502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153558 q = 0) : d155503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153558, d155503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153558, d155503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153559 q = 0) : d155504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153559, d155504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153559, d155504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153560 q = 0) : d155505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153560, d155505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153560, d155505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13855 (p : Pattern) (selected : d153565 p = 0) : d155493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153510 q = 0) : d155483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153510, d155483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13846 q selected
    | true =>
      simp only [d153510, d155483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153511 q = 0) : d155484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153511, d155484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153511, d155484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153562 q = 0) : d155490 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153562, d155490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153562, d155490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153563 q = 0) : d155491 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153563, d155491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153563, d155491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153564 q = 0) : d155492 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153564, d155492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153564, d155492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153565 q = 0) : d155493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153565, d155493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153565, d155493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13856 (p : Pattern) (selected : d153571 p = 0) : d155512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153566 q = 0) : d155507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153566, d155507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13855 q selected
    | true =>
      simp only [d153566, d155507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153567 q = 0) : d155508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153567, d155508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153567, d155508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153568 q = 0) : d155509 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153568, d155509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153568, d155509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153569 q = 0) : d155510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153569, d155510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153569, d155510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153570 q = 0) : d155511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153570, d155511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153570, d155511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153571 q = 0) : d155512 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153571, d155512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153571, d155512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13857 (p : Pattern) (selected : d153577 p = 0) : d155518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153315 q = 0) : d155328 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153315, d155328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153315, d155328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13805 q selected
  have h2 (q : Pattern) (selected : d153316 q = 0) : d155329 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153316, d155329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153316, d155329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153325 q = 0) : d155338 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153325, d155338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13805 q selected
    | true =>
      simp only [d153325, d155338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13808 q selected
  have h4 (q : Pattern) (selected : d153326 q = 0) : d155339 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153326, d155339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153326, d155339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153327 q = 0) : d155340 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153327, d155340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153327, d155340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153449 q = 0) : d155422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153449, d155422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13827 q selected
    | true =>
      simp only [d153449, d155422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13836 q selected
  have h7 (q : Pattern) (selected : d153462 q = 0) : d155435 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153462, d155435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13837 q selected
    | true =>
      simp only [d153462, d155435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13838 q selected
  have h8 (q : Pattern) (selected : d153463 q = 0) : d155436 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153463, d155436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153463, d155436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153464 q = 0) : d155437 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153464, d155437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153464, d155437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d153465 q = 0) : d155438 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153465, d155438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153465, d155438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153469 q = 0) : d155442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153469, d155442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153469, d155442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13839 q selected
  have h12 (q : Pattern) (selected : d153471 q = 0) : d155444 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153471, d155444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153471, d155444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13840 q selected
  have h13 (q : Pattern) (selected : d153472 q = 0) : d155445 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153472, d155445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153472, d155445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153473 q = 0) : d155446 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153473, d155446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153473, d155446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153474 q = 0) : d155447 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153474, d155447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153474, d155447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153475 q = 0) : d155448 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153475, d155448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153475, d155448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153561 q = 0) : d155506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153561, d155506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153561, d155506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13854 q selected
  have h18 (q : Pattern) (selected : d153572 q = 0) : d155513 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153572, d155513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153572, d155513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13856 q selected
  have h19 (q : Pattern) (selected : d153573 q = 0) : d155514 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153573, d155514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d153573, d155514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d153574 q = 0) : d155515 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153574, d155515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153574, d155515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d153575 q = 0) : d155516 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153575, d155516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d153575, d155516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d153576 q = 0) : d155517 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153576, d155517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153576, d155517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d153577 q = 0) : d155518 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d153577, d155518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153577, d155518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro13858 (p : Pattern) (selected : d153583 p = 0) : d155524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153578 q = 0) : d155519 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d153578, d155519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153578, d155519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13857 q selected
  have h2 (q : Pattern) (selected : d153579 q = 0) : d155520 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d153579, d155520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153579, d155520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153580 q = 0) : d155521 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d153580, d155521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153580, d155521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153581 q = 0) : d155522 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d153581, d155522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153581, d155522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153582 q = 0) : d155523 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d153582, d155523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153582, d155523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153583 q = 0) : d155524 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d153583, d155524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153583, d155524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13859 (p : Pattern) (selected : d153587 p = 0) : d155528 p = 1 := by
  have h0 (q : Pattern) (selected : d1088 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1089 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d537 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro276 q selected
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d538 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153586 q = 0) : d155527 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153586, d155527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153586, d155527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153587 q = 0) : d155528 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153587, d155528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153587, d155528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro13860 (p : Pattern) (selected : d153593 p = 0) : d155534 p = 1 := by
  have h0 (q : Pattern) (selected : d1094 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1095 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153592 q = 0) : d155533 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153592, d155533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153592, d155533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153593 q = 0) : d155534 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153593, d155534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153593, d155534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro13861 (p : Pattern) (selected : d153599 p = 0) : d155540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153588 q = 0) : d155529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153588, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13859 q selected
    | true =>
      simp only [d153588, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153589 q = 0) : d155530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153589, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153589, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153590 q = 0) : d155531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153590, d155531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153590, d155531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153591 q = 0) : d155532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153591, d155532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153591, d155532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153594 q = 0) : d155535 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153594, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13860 q selected
    | true =>
      simp only [d153594, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153595 q = 0) : d155536 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153595, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153595, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153596 q = 0) : d155537 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153596, d155537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153596, d155537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153597 q = 0) : d155538 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153597, d155538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153597, d155538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153598 q = 0) : d155539 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153598, d155539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153598, d155539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153354 q = 0) : d155367 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13814 q selected
    | true =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153355 q = 0) : d155368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153356 q = 0) : d155369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153356, d155369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153356, d155369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153357 q = 0) : d155370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153357, d155370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153357, d155370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153133 q = 0) : d155188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153134 q = 0) : d155189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153358 q = 0) : d155371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153358, d155371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153358, d155371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153599 q = 0) : d155540 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153599, d155540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153599, d155540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro13862 (p : Pattern) (selected : d153601 p = 0) : d155542 p = 1 := by
  have h0 (q : Pattern) (selected : d1104 q = 0) : d52685 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d1104, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1105 q = 0) : d52686 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1105, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153600 q = 0) : d155541 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153600, d155541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153600, d155541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153601 q = 0) : d155542 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153601, d155542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153601, d155542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro13863 (p : Pattern) (selected : d153608 p = 0) : d155549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153594 q = 0) : d155535 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153594, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13860 q selected
    | true =>
      simp only [d153594, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153595 q = 0) : d155536 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153595, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153595, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153596 q = 0) : d155537 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153596, d155537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153596, d155537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153597 q = 0) : d155538 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153597, d155538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153597, d155538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153602 q = 0) : d155543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153602, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13862 q selected
    | true =>
      simp only [d153602, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153603 q = 0) : d155544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153603, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153603, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153604 q = 0) : d155545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153604, d155545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153604, d155545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153605 q = 0) : d155546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153605, d155546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153605, d155546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153606 q = 0) : d155547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153606, d155547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153606, d155547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153133 q = 0) : d155188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153134 q = 0) : d155189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d153607 q = 0) : d155548 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153607, d155548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153607, d155548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153608 q = 0) : d155549 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153608, d155549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153608, d155549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13864 (p : Pattern) (selected : d153613 p = 0) : d155554 p = 1 := by
  have h0 (q : Pattern) (selected : d5012 q = 0) : d69102 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5012, d69102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2798 q selected
    | true =>
      simp only [d5012, d69102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d5013 q = 0) : d69103 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5013, d69103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5013, d69103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153612 q = 0) : d155553 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153612, d155553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153612, d155553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153613 q = 0) : d155554 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153613, d155554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153613, d155554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro13865 (p : Pattern) (selected : d153619 p = 0) : d155560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153614 q = 0) : d155555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153614, d155555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13864 q selected
    | true =>
      simp only [d153614, d155555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153615 q = 0) : d155556 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153615, d155556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153615, d155556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153616 q = 0) : d155557 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153616, d155557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153616, d155557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153617 q = 0) : d155558 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153617, d155558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153617, d155558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153618 q = 0) : d155559 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153618, d155559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153618, d155559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153619 q = 0) : d155560 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153619, d155560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153619, d155560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13866 (p : Pattern) (selected : d153625 p = 0) : d155566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153602 q = 0) : d155543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153602, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13862 q selected
    | true =>
      simp only [d153602, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153603 q = 0) : d155544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153603, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153603, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153604 q = 0) : d155545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153604, d155545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153604, d155545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153605 q = 0) : d155546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153605, d155546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153605, d155546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153624 q = 0) : d155565 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153624, d155565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153624, d155565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153625 q = 0) : d155566 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153625, d155566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153625, d155566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13867 (p : Pattern) (selected : d153631 p = 0) : d155572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153609 q = 0) : d155550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153609, d155550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13861 q selected
    | true =>
      simp only [d153609, d155550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13863 q selected
  have h2 (q : Pattern) (selected : d153610 q = 0) : d155551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153610, d155551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153610, d155551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153611 q = 0) : d155552 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153611, d155552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153611, d155552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153620 q = 0) : d155561 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153620, d155561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13863 q selected
    | true =>
      simp only [d153620, d155561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13865 q selected
  have h5 (q : Pattern) (selected : d153621 q = 0) : d155562 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153621, d155562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153621, d155562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153622 q = 0) : d155563 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153622, d155563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153622, d155563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153623 q = 0) : d155564 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153623, d155564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153623, d155564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153626 q = 0) : d155567 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153626, d155567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13863 q selected
    | true =>
      simp only [d153626, d155567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13866 q selected
  have h9 (q : Pattern) (selected : d153627 q = 0) : d155568 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153627, d155568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153627, d155568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153628 q = 0) : d155569 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153628, d155569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153628, d155569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153629 q = 0) : d155570 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153629, d155570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153629, d155570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153630 q = 0) : d155571 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153630, d155571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153630, d155571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153631 q = 0) : d155572 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153631, d155572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153631, d155572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13868 (p : Pattern) (selected : d153635 p = 0) : d155576 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153626 q = 0) : d155567 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153626, d155567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13863 q selected
    | true =>
      simp only [d153626, d155567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13866 q selected
  have h2 (q : Pattern) (selected : d153627 q = 0) : d155568 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153627, d155568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153627, d155568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153628 q = 0) : d155569 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153628, d155569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153628, d155569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153629 q = 0) : d155570 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153629, d155570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153629, d155570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153634 q = 0) : d155575 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153634, d155575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153634, d155575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153635 q = 0) : d155576 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153635, d155576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153635, d155576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13869 (p : Pattern) (selected : d153641 p = 0) : d155582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153632 q = 0) : d155573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13867 q selected
    | true =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153633 q = 0) : d155574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153638 q = 0) : d155579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153639 q = 0) : d155580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153639, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153639, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153640 q = 0) : d155581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153640, d155581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153640, d155581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153641 q = 0) : d155582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153641, d155582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153641, d155582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13870 (p : Pattern) (selected : d153645 p = 0) : d155586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153642 q = 0) : d155583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153643 q = 0) : d155584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153643, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153643, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153644 q = 0) : d155585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153644, d155585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153644, d155585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153645 q = 0) : d155586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153645, d155586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153645, d155586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13871 (p : Pattern) (selected : d153651 p = 0) : d155592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153646 q = 0) : d155587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153646, d155587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13869 q selected
    | true =>
      simp only [d153646, d155587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13870 q selected
  have h2 (q : Pattern) (selected : d153647 q = 0) : d155588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153647, d155588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153647, d155588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153648 q = 0) : d155589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153648, d155589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153648, d155589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153649 q = 0) : d155590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153649, d155590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153649, d155590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153650 q = 0) : d155591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153650, d155591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153650, d155591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153651 q = 0) : d155592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153651, d155592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153651, d155592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13872 (p : Pattern) (selected : d153654 p = 0) : d155595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153632 q = 0) : d155573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13867 q selected
    | true =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153633 q = 0) : d155574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153638 q = 0) : d155579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153639 q = 0) : d155580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153639, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153639, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153640 q = 0) : d155581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153640, d155581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153640, d155581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153654 q = 0) : d155595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153654, d155595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153654, d155595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13873 (p : Pattern) (selected : d153655 p = 0) : d155596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153642 q = 0) : d155583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153643 q = 0) : d155584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153643, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153643, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153644 q = 0) : d155585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153644, d155585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153644, d155585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153655 q = 0) : d155596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153655, d155596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153655, d155596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13874 (p : Pattern) (selected : d153661 p = 0) : d155602 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153646 q = 0) : d155587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153646, d155587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13869 q selected
    | true =>
      simp only [d153646, d155587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13870 q selected
  have h2 (q : Pattern) (selected : d153647 q = 0) : d155588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153647, d155588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153647, d155588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153648 q = 0) : d155589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153648, d155589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153648, d155589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153649 q = 0) : d155590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153649, d155590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153649, d155590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153650 q = 0) : d155591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153650, d155591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153650, d155591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153656 q = 0) : d155597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153656, d155597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13872 q selected
    | true =>
      simp only [d153656, d155597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13873 q selected
  have h7 (q : Pattern) (selected : d153657 q = 0) : d155598 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153657, d155598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153657, d155598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153658 q = 0) : d155599 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153658, d155599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153658, d155599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153659 q = 0) : d155600 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153659, d155600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153659, d155600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153660 q = 0) : d155601 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153660, d155601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153660, d155601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153661 q = 0) : d155602 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153661, d155602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153661, d155602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13875 (p : Pattern) (selected : d153666 p = 0) : d155607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153632 q = 0) : d155573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13867 q selected
    | true =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153633 q = 0) : d155574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153638 q = 0) : d155579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153639 q = 0) : d155580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153639, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153639, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153665 q = 0) : d155606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153665, d155606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153665, d155606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153666 q = 0) : d155607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153666, d155607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153666, d155607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13876 (p : Pattern) (selected : d153668 p = 0) : d155609 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153642 q = 0) : d155583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153643 q = 0) : d155584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153643, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153643, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153667 q = 0) : d155608 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153667, d155608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153667, d155608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153668 q = 0) : d155609 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153668, d155609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153668, d155609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13877 (p : Pattern) (selected : d153675 p = 0) : d155616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153632 q = 0) : d155573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13867 q selected
    | true =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153633 q = 0) : d155574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153638 q = 0) : d155579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153673 q = 0) : d155614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153673, d155614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153673, d155614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153674 q = 0) : d155615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153674, d155615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153674, d155615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153675 q = 0) : d155616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153675, d155616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153675, d155616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13878 (p : Pattern) (selected : d153678 p = 0) : d155619 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153642 q = 0) : d155583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153676 q = 0) : d155617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153676, d155617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153676, d155617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153677 q = 0) : d155618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153677, d155618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153677, d155618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153678 q = 0) : d155619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153678, d155619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153678, d155619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13879 (p : Pattern) (selected : d153683 p = 0) : d155624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d822 q = 0) : d52499 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro333 q selected
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d823 q = 0) : d52500 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d828 q = 0) : d52505 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro334 q selected
    | true =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d829 q = 0) : d52506 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153682 q = 0) : d155623 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153682, d155623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153682, d155623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153683 q = 0) : d155624 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153683, d155624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153683, d155624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13880 (p : Pattern) (selected : d153690 p = 0) : d155631 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153684 q = 0) : d155625 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153684, d155625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13879 q selected
    | true =>
      simp only [d153684, d155625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153685 q = 0) : d155626 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153685, d155626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153685, d155626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153686 q = 0) : d155627 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153686, d155627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153686, d155627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153687 q = 0) : d155628 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153687, d155628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153687, d155628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153588 q = 0) : d155529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153588, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13859 q selected
    | true =>
      simp only [d153588, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153589 q = 0) : d155530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153589, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153589, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153590 q = 0) : d155531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153590, d155531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153590, d155531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153591 q = 0) : d155532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153591, d155532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153591, d155532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153688 q = 0) : d155629 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153688, d155629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153688, d155629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153354 q = 0) : d155367 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13814 q selected
    | true =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153355 q = 0) : d155368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153356 q = 0) : d155369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153356, d155369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153356, d155369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153357 q = 0) : d155370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153357, d155370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153357, d155370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d153689 q = 0) : d155630 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153689, d155630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153689, d155630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153690 q = 0) : d155631 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153690, d155631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153690, d155631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13881 (p : Pattern) (selected : d153695 p = 0) : d155636 p = 1 := by
  have h0 (q : Pattern) (selected : d9772 q = 0) : d101293 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6640 q selected
    | true =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6671 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d9773 q = 0) : d101294 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153694 q = 0) : d155635 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153694, d155635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153694, d155635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d153695 q = 0) : d155636 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153695, d155636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153695, d155636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro13882 (p : Pattern) (selected : d153701 p = 0) : d155642 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153696 q = 0) : d155637 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153696, d155637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13881 q selected
    | true =>
      simp only [d153696, d155637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153697 q = 0) : d155638 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153697, d155638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153697, d155638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153698 q = 0) : d155639 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153698, d155639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153698, d155639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153699 q = 0) : d155640 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153699, d155640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153699, d155640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153133 q = 0) : d155188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153133, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153134 q = 0) : d155189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153134, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153700 q = 0) : d155641 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153700, d155641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153700, d155641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153607 q = 0) : d155548 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153607, d155548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153607, d155548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153701 q = 0) : d155642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153701, d155642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153701, d155642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13883 (p : Pattern) (selected : d153707 p = 0) : d155648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153691 q = 0) : d155632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153691, d155632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13880 q selected
    | true =>
      simp only [d153691, d155632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13861 q selected
  have h2 (q : Pattern) (selected : d153692 q = 0) : d155633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153692, d155633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153692, d155633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153693 q = 0) : d155634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153693, d155634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153693, d155634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153702 q = 0) : d155643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153702, d155643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13861 q selected
    | true =>
      simp only [d153702, d155643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13882 q selected
  have h5 (q : Pattern) (selected : d153703 q = 0) : d155644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153703, d155644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153703, d155644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153704 q = 0) : d155645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153704, d155645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153704, d155645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153705 q = 0) : d155646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153705, d155646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153705, d155646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153609 q = 0) : d155550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153609, d155550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13861 q selected
    | true =>
      simp only [d153609, d155550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13863 q selected
  have h9 (q : Pattern) (selected : d153610 q = 0) : d155551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153610, d155551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153610, d155551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153611 q = 0) : d155552 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153611, d155552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153611, d155552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153620 q = 0) : d155561 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153620, d155561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13863 q selected
    | true =>
      simp only [d153620, d155561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13865 q selected
  have h12 (q : Pattern) (selected : d153621 q = 0) : d155562 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153621, d155562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153621, d155562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153622 q = 0) : d155563 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153622, d155563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153622, d155563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153623 q = 0) : d155564 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153623, d155564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153623, d155564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153706 q = 0) : d155647 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153706, d155647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153706, d155647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153707 q = 0) : d155648 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153707, d155648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153707, d155648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13884 (p : Pattern) (selected : d153712 p = 0) : d155653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153609 q = 0) : d155550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153609, d155550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13861 q selected
    | true =>
      simp only [d153609, d155550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13863 q selected
  have h2 (q : Pattern) (selected : d153610 q = 0) : d155551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153610, d155551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153610, d155551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153611 q = 0) : d155552 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153611, d155552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153611, d155552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153620 q = 0) : d155561 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153620, d155561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13863 q selected
    | true =>
      simp only [d153620, d155561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13865 q selected
  have h5 (q : Pattern) (selected : d153621 q = 0) : d155562 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153621, d155562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153621, d155562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153622 q = 0) : d155563 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153622, d155563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153622, d155563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153623 q = 0) : d155564 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153623, d155564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153623, d155564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153710 q = 0) : d155651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153710, d155651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153710, d155651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153711 q = 0) : d155652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153711, d155652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153711, d155652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153712 q = 0) : d155653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153712, d155653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153712, d155653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13885 (p : Pattern) (selected : d153718 p = 0) : d155659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153708 q = 0) : d155649 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153708, d155649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13883 q selected
    | true =>
      simp only [d153708, d155649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153709 q = 0) : d155650 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153709, d155650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153709, d155650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153713 q = 0) : d155654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153713, d155654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13884 q selected
    | true =>
      simp only [d153713, d155654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153714 q = 0) : d155655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153714, d155655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153714, d155655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153715 q = 0) : d155656 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153715, d155656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153715, d155656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153716 q = 0) : d155657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153716, d155657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153716, d155657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153717 q = 0) : d155658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153717, d155658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153717, d155658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153718 q = 0) : d155659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153718, d155659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153718, d155659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13886 (p : Pattern) (selected : d153722 p = 0) : d155663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153713 q = 0) : d155654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153713, d155654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13884 q selected
    | true =>
      simp only [d153713, d155654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153714 q = 0) : d155655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153714, d155655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153714, d155655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153719 q = 0) : d155660 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153719, d155660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153719, d155660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153720 q = 0) : d155661 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153720, d155661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153720, d155661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153721 q = 0) : d155662 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153721, d155662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153721, d155662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153722 q = 0) : d155663 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153722, d155663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153722, d155663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13887 (p : Pattern) (selected : d153725 p = 0) : d155528 p = 1 := by
  have h0 (q : Pattern) (selected : d1237 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1237, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro339 q selected
    | true =>
      simp only [d1237, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro412 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1238 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1238, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1238, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d862 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d862, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro340 q selected
    | true =>
      simp only [d862, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d863 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d863, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d863, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153724 q = 0) : d155527 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153724, d155527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153724, d155527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153725 q = 0) : d155528 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153725, d155528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153725, d155528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro13888 (p : Pattern) (selected : d153731 p = 0) : d155534 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1250 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d344 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d345 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153730 q = 0) : d155533 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153730, d155533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153730, d155533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153731 q = 0) : d155534 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153731, d155534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153731, d155534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro13889 (p : Pattern) (selected : d153738 p = 0) : d155366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9902 q = 0) : d101161 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9902, d101161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6688 q selected
    | true =>
      simp only [d9902, d101161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9903 q = 0) : d101162 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9903, d101162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9903, d101162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153737 q = 0) : d155365 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153737, d155365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153737, d155365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153738 q = 0) : d155366 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153738, d155366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153738, d155366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro13890 (p : Pattern) (selected : d153744 p = 0) : d155540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153726 q = 0) : d155529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153726, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13887 q selected
    | true =>
      simp only [d153726, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153727 q = 0) : d155530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153727, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153727, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153728 q = 0) : d155531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153728, d155531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153728, d155531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153729 q = 0) : d155532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153729, d155532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153729, d155532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153732 q = 0) : d155535 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153732, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13888 q selected
    | true =>
      simp only [d153732, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153733 q = 0) : d155536 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153733, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153733, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153734 q = 0) : d155537 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153734, d155537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153734, d155537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153735 q = 0) : d155538 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153735, d155538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153735, d155538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153736 q = 0) : d155539 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153736, d155539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153736, d155539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153739 q = 0) : d155367 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153739, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13889 q selected
    | true =>
      simp only [d153739, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153740 q = 0) : d155368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153740, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153740, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153741 q = 0) : d155369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153741, d155369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153741, d155369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153742 q = 0) : d155370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153742, d155370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153742, d155370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d153386 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13820 q selected
    | true =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153387 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153388 q = 0) : d155188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153388, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153388, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153389 q = 0) : d155189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153389, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153389, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153743 q = 0) : d155371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153743, d155371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153743, d155371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153744 q = 0) : d155540 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153744, d155540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153744, d155540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro13891 (p : Pattern) (selected : d153746 p = 0) : d155542 p = 1 := by
  have h0 (q : Pattern) (selected : d1259 q = 0) : d52685 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1259, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d1259, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1260 q = 0) : d52686 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1260, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1260, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153745 q = 0) : d155541 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153745, d155541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153745, d155541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153746 q = 0) : d155542 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153746, d155542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153746, d155542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro13892 (p : Pattern) (selected : d153753 p = 0) : d155549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153732 q = 0) : d155535 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153732, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13888 q selected
    | true =>
      simp only [d153732, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153733 q = 0) : d155536 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153733, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153733, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153734 q = 0) : d155537 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153734, d155537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153734, d155537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153735 q = 0) : d155538 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153735, d155538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153735, d155538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153747 q = 0) : d155543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153747, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13891 q selected
    | true =>
      simp only [d153747, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153748 q = 0) : d155544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153748, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153748, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153749 q = 0) : d155545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153749, d155545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153749, d155545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153750 q = 0) : d155546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153750, d155546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153750, d155546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153751 q = 0) : d155547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153751, d155547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153751, d155547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153386 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13820 q selected
    | true =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153387 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153388 q = 0) : d155188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153388, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153388, d155188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153389 q = 0) : d155189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153389, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153389, d155189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d153752 q = 0) : d155548 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153752, d155548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153752, d155548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153753 q = 0) : d155549 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153753, d155549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153753, d155549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13893 (p : Pattern) (selected : d153758 p = 0) : d155554 p = 1 := by
  have h0 (q : Pattern) (selected : d9937 q = 0) : d69102 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9937, d69102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6653 q selected
    | true =>
      simp only [d9937, d69102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d9938 q = 0) : d69103 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9938, d69103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9938, d69103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d153757 q = 0) : d155553 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d153757, d155553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153757, d155553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153758 q = 0) : d155554 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d153758, d155554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153758, d155554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro13894 (p : Pattern) (selected : d153764 p = 0) : d155560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153759 q = 0) : d155555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153759, d155555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13893 q selected
    | true =>
      simp only [d153759, d155555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153760 q = 0) : d155556 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153760, d155556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153760, d155556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153761 q = 0) : d155557 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153761, d155557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153761, d155557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153762 q = 0) : d155558 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153762, d155558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153762, d155558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153763 q = 0) : d155559 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153763, d155559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153763, d155559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153764 q = 0) : d155560 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153764, d155560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153764, d155560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13895 (p : Pattern) (selected : d153770 p = 0) : d155566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153747 q = 0) : d155543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153747, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13891 q selected
    | true =>
      simp only [d153747, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153748 q = 0) : d155544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153748, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153748, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153749 q = 0) : d155545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153749, d155545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153749, d155545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153750 q = 0) : d155546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153750, d155546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153750, d155546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153769 q = 0) : d155565 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153769, d155565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153769, d155565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153770 q = 0) : d155566 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153770, d155566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153770, d155566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13896 (p : Pattern) (selected : d153776 p = 0) : d155572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153754 q = 0) : d155550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153754, d155550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13890 q selected
    | true =>
      simp only [d153754, d155550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13892 q selected
  have h2 (q : Pattern) (selected : d153755 q = 0) : d155551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153755, d155551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153755, d155551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153756 q = 0) : d155552 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153756, d155552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153756, d155552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153765 q = 0) : d155561 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153765, d155561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13892 q selected
    | true =>
      simp only [d153765, d155561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13894 q selected
  have h5 (q : Pattern) (selected : d153766 q = 0) : d155562 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153766, d155562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153766, d155562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153767 q = 0) : d155563 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153767, d155563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153767, d155563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153768 q = 0) : d155564 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153768, d155564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153768, d155564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153771 q = 0) : d155567 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153771, d155567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13892 q selected
    | true =>
      simp only [d153771, d155567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13895 q selected
  have h9 (q : Pattern) (selected : d153772 q = 0) : d155568 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153772, d155568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153772, d155568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153773 q = 0) : d155569 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153773, d155569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153773, d155569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153774 q = 0) : d155570 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153774, d155570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153774, d155570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153775 q = 0) : d155571 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153775, d155571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153775, d155571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153776 q = 0) : d155572 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153776, d155572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153776, d155572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13897 (p : Pattern) (selected : d153780 p = 0) : d155576 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153771 q = 0) : d155567 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153771, d155567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13892 q selected
    | true =>
      simp only [d153771, d155567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13895 q selected
  have h2 (q : Pattern) (selected : d153772 q = 0) : d155568 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153772, d155568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153772, d155568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153773 q = 0) : d155569 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153773, d155569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153773, d155569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153774 q = 0) : d155570 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153774, d155570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153774, d155570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153779 q = 0) : d155575 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153779, d155575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153779, d155575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153780 q = 0) : d155576 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153780, d155576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153780, d155576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13898 (p : Pattern) (selected : d153786 p = 0) : d155582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153777 q = 0) : d155573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153777, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13896 q selected
    | true =>
      simp only [d153777, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153778 q = 0) : d155574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153778, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153778, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153781 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153781, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13897 q selected
    | true =>
      simp only [d153781, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153782 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153782, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153782, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153783 q = 0) : d155579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153783, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153783, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153784 q = 0) : d155580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153784, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153784, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153785 q = 0) : d155581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153785, d155581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153785, d155581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153786 q = 0) : d155582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153786, d155582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153786, d155582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13899 (p : Pattern) (selected : d153790 p = 0) : d155586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153781 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153781, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13897 q selected
    | true =>
      simp only [d153781, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153782 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153782, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153782, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153787 q = 0) : d155583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153787, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153787, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153788 q = 0) : d155584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153788, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153788, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153789 q = 0) : d155585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153789, d155585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153789, d155585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153790 q = 0) : d155586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153790, d155586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153790, d155586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13900 (p : Pattern) (selected : d153796 p = 0) : d155669 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153632 q = 0) : d155573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13867 q selected
    | true =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153633 q = 0) : d155574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153793 q = 0) : d155666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153793, d155666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153793, d155666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153794 q = 0) : d155667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153794, d155667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153794, d155667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153795 q = 0) : d155668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153795, d155668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153795, d155668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153796 q = 0) : d155669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153796, d155669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153796, d155669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13901 (p : Pattern) (selected : d153802 p = 0) : d155675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153669 q = 0) : d155610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153669, d155610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13875 q selected
    | true =>
      simp only [d153669, d155610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13876 q selected
  have h2 (q : Pattern) (selected : d153670 q = 0) : d155611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153670, d155611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153670, d155611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153671 q = 0) : d155612 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153671, d155612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153671, d155612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153672 q = 0) : d155613 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153672, d155613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153672, d155613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153679 q = 0) : d155620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153679, d155620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13877 q selected
    | true =>
      simp only [d153679, d155620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13878 q selected
  have h6 (q : Pattern) (selected : d153680 q = 0) : d155621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153680, d155621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153680, d155621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153681 q = 0) : d155622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153681, d155622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153681, d155622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153723 q = 0) : d155664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153723, d155664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13885 q selected
    | true =>
      simp only [d153723, d155664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13886 q selected
  have h9 (q : Pattern) (selected : d153791 q = 0) : d155587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153791, d155587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13898 q selected
    | true =>
      simp only [d153791, d155587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13899 q selected
  have h10 (q : Pattern) (selected : d153792 q = 0) : d155665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153792, d155665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153792, d155665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153797 q = 0) : d155670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153797, d155670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13900 q selected
    | true =>
      simp only [d153797, d155670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153798 q = 0) : d155671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153798, d155671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153798, d155671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153799 q = 0) : d155672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153799, d155672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153799, d155672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153800 q = 0) : d155673 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153800, d155673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153800, d155673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153801 q = 0) : d155674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153801, d155674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153801, d155674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153802 q = 0) : d155675 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153802, d155675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153802, d155675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro13902 (p : Pattern) (selected : d153803 p = 0) : d155676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153632 q = 0) : d155573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13867 q selected
    | true =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153633 q = 0) : d155574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153638 q = 0) : d155579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153639 q = 0) : d155580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153639, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153639, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153665 q = 0) : d155606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153665, d155606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153665, d155606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153803 q = 0) : d155676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153803, d155676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153803, d155676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13903 (p : Pattern) (selected : d153804 p = 0) : d155677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153642 q = 0) : d155583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153643 q = 0) : d155584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153643, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153643, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153667 q = 0) : d155608 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153667, d155608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153667, d155608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153804 q = 0) : d155677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153804, d155677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153804, d155677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13904 (p : Pattern) (selected : d153809 p = 0) : d155682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153632 q = 0) : d155573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13867 q selected
    | true =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153633 q = 0) : d155574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153638 q = 0) : d155579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153638, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153673 q = 0) : d155614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153673, d155614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153673, d155614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153674 q = 0) : d155615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153674, d155615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153674, d155615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153809 q = 0) : d155682 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153809, d155682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153809, d155682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13905 (p : Pattern) (selected : d153810 p = 0) : d155683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153642 q = 0) : d155583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153642, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153676 q = 0) : d155617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153676, d155617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153676, d155617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153677 q = 0) : d155618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153677, d155618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153677, d155618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153810 q = 0) : d155683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153810, d155683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153810, d155683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13906 (p : Pattern) (selected : d153814 p = 0) : d155687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153708 q = 0) : d155649 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153708, d155649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13883 q selected
    | true =>
      simp only [d153708, d155649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153709 q = 0) : d155650 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153709, d155650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153709, d155650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153713 q = 0) : d155654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153713, d155654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13884 q selected
    | true =>
      simp only [d153713, d155654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153714 q = 0) : d155655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153714, d155655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153714, d155655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153715 q = 0) : d155656 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153715, d155656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153715, d155656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153716 q = 0) : d155657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153716, d155657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153716, d155657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153717 q = 0) : d155658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153717, d155658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153717, d155658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153814 q = 0) : d155687 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153814, d155687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153814, d155687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13907 (p : Pattern) (selected : d153815 p = 0) : d155688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153713 q = 0) : d155654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153713, d155654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13884 q selected
    | true =>
      simp only [d153713, d155654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153714 q = 0) : d155655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153714, d155655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153714, d155655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153636 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13868 q selected
    | true =>
      simp only [d153636, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153637 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153637, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153719 q = 0) : d155660 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153719, d155660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153719, d155660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153720 q = 0) : d155661 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153720, d155661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153720, d155661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153721 q = 0) : d155662 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153721, d155662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153721, d155662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153815 q = 0) : d155688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153815, d155688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153815, d155688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13908 (p : Pattern) (selected : d153817 p = 0) : d155595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153777 q = 0) : d155573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153777, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13896 q selected
    | true =>
      simp only [d153777, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153778 q = 0) : d155574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153778, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153778, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153781 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153781, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13897 q selected
    | true =>
      simp only [d153781, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153782 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153782, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153782, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153783 q = 0) : d155579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153783, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153783, d155579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153784 q = 0) : d155580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153784, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153784, d155580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153785 q = 0) : d155581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153785, d155581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153785, d155581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153817 q = 0) : d155595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153817, d155595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153817, d155595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13909 (p : Pattern) (selected : d153818 p = 0) : d155596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153781 q = 0) : d155577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153781, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13897 q selected
    | true =>
      simp only [d153781, d155577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153782 q = 0) : d155578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153782, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153782, d155578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153787 q = 0) : d155583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153787, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153787, d155583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153788 q = 0) : d155584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153788, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153788, d155584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153789 q = 0) : d155585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153789, d155585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153789, d155585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153818 q = 0) : d155596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153818, d155596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153818, d155596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13910 (p : Pattern) (selected : d153821 p = 0) : d155691 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153632 q = 0) : d155573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13867 q selected
    | true =>
      simp only [d153632, d155573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153633 q = 0) : d155574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153633, d155574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153793 q = 0) : d155666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153793, d155666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153793, d155666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153794 q = 0) : d155667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153794, d155667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153794, d155667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153795 q = 0) : d155668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153795, d155668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153795, d155668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153821 q = 0) : d155691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153821, d155691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153821, d155691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13911 (p : Pattern) (selected : d153827 p = 0) : d155697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153669 q = 0) : d155610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153669, d155610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13875 q selected
    | true =>
      simp only [d153669, d155610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13876 q selected
  have h2 (q : Pattern) (selected : d153670 q = 0) : d155611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153670, d155611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153670, d155611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153671 q = 0) : d155612 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153671, d155612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153671, d155612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153672 q = 0) : d155613 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153672, d155613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153672, d155613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153679 q = 0) : d155620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153679, d155620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13877 q selected
    | true =>
      simp only [d153679, d155620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13878 q selected
  have h6 (q : Pattern) (selected : d153680 q = 0) : d155621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153680, d155621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153680, d155621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153681 q = 0) : d155622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153681, d155622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153681, d155622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153723 q = 0) : d155664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153723, d155664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13885 q selected
    | true =>
      simp only [d153723, d155664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13886 q selected
  have h9 (q : Pattern) (selected : d153791 q = 0) : d155587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153791, d155587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13898 q selected
    | true =>
      simp only [d153791, d155587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13899 q selected
  have h10 (q : Pattern) (selected : d153792 q = 0) : d155665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153792, d155665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153792, d155665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153797 q = 0) : d155670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153797, d155670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13900 q selected
    | true =>
      simp only [d153797, d155670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153798 q = 0) : d155671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153798, d155671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153798, d155671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153799 q = 0) : d155672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153799, d155672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153799, d155672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153800 q = 0) : d155673 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153800, d155673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153800, d155673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153801 q = 0) : d155674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153801, d155674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153801, d155674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153805 q = 0) : d155678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153805, d155678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13902 q selected
    | true =>
      simp only [d153805, d155678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13903 q selected
  have h17 (q : Pattern) (selected : d153806 q = 0) : d155679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153806, d155679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153806, d155679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d153807 q = 0) : d155680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153807, d155680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d153807, d155680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d153808 q = 0) : d155681 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153808, d155681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153808, d155681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d153811 q = 0) : d155684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153811, d155684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13904 q selected
    | true =>
      simp only [d153811, d155684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13905 q selected
  have h21 (q : Pattern) (selected : d153812 q = 0) : d155685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153812, d155685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153812, d155685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d153813 q = 0) : d155686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153813, d155686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153813, d155686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d153816 q = 0) : d155689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153816, d155689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13906 q selected
    | true =>
      simp only [d153816, d155689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13907 q selected
  have h24 (q : Pattern) (selected : d153819 q = 0) : d155597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153819, d155597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13908 q selected
    | true =>
      simp only [d153819, d155597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13909 q selected
  have h25 (q : Pattern) (selected : d153820 q = 0) : d155690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153820, d155690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d153820, d155690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d153822 q = 0) : d155692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153822, d155692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13910 q selected
    | true =>
      simp only [d153822, d155692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d153823 q = 0) : d155693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153823, d155693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d153823, d155693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d153824 q = 0) : d155694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153824, d155694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d153824, d155694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d153825 q = 0) : d155695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153825, d155695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d153825, d155695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d153826 q = 0) : d155696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153826, d155696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153826, d155696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d153827 q = 0) : d155697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153827, d155697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153827, d155697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro13912 (p : Pattern) (selected : d153839 p = 0) : d155709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153829 q = 0) : d155699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153829, d155699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13886 q selected
    | true =>
      simp only [d153829, d155699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13870 q selected
  have h2 (q : Pattern) (selected : d153830 q = 0) : d155700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153830, d155700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153830, d155700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153831 q = 0) : d155701 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153831, d155701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153831, d155701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153832 q = 0) : d155702 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153832, d155702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153832, d155702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153833 q = 0) : d155703 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153833, d155703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153833, d155703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153834 q = 0) : d155704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153834, d155704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13870 q selected
    | true =>
      simp only [d153834, d155704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153835 q = 0) : d155705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153835, d155705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153835, d155705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153836 q = 0) : d155706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153836, d155706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153836, d155706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153837 q = 0) : d155707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153837, d155707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153837, d155707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153838 q = 0) : d155708 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153838, d155708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153838, d155708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153839 q = 0) : d155709 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153839, d155709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153839, d155709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13913 (p : Pattern) (selected : d153845 p = 0) : d155715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153834 q = 0) : d155704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153834, d155704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13870 q selected
    | true =>
      simp only [d153834, d155704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153835 q = 0) : d155705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153835, d155705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153835, d155705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153836 q = 0) : d155706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153836, d155706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153836, d155706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153837 q = 0) : d155707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153837, d155707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153837, d155707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153838 q = 0) : d155708 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153838, d155708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153838, d155708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153840 q = 0) : d155710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153840, d155710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13873 q selected
    | true =>
      simp only [d153840, d155710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153841 q = 0) : d155711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153841, d155711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153841, d155711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153842 q = 0) : d155712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153842, d155712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153842, d155712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153843 q = 0) : d155713 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153843, d155713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153843, d155713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153844 q = 0) : d155714 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153844, d155714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153844, d155714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153845 q = 0) : d155715 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153845, d155715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153845, d155715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13914 (p : Pattern) (selected : d153852 p = 0) : d155722 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153816 q = 0) : d155689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153816, d155689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13906 q selected
    | true =>
      simp only [d153816, d155689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13907 q selected
  have h2 (q : Pattern) (selected : d153819 q = 0) : d155597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153819, d155597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13908 q selected
    | true =>
      simp only [d153819, d155597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13909 q selected
  have h3 (q : Pattern) (selected : d153820 q = 0) : d155690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153820, d155690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153820, d155690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153822 q = 0) : d155692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153822, d155692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13910 q selected
    | true =>
      simp only [d153822, d155692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153823 q = 0) : d155693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153823, d155693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153823, d155693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153824 q = 0) : d155694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153824, d155694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153824, d155694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153850 q = 0) : d155720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153850, d155720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153850, d155720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153851 q = 0) : d155721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153851, d155721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153851, d155721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153852 q = 0) : d155722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153852, d155722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153852, d155722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13915 (p : Pattern) (selected : d153854 p = 0) : d155724 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153840 q = 0) : d155710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153840, d155710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13873 q selected
    | true =>
      simp only [d153840, d155710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153841 q = 0) : d155711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153841, d155711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153841, d155711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153842 q = 0) : d155712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153842, d155712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153842, d155712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153843 q = 0) : d155713 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153843, d155713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153843, d155713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153844 q = 0) : d155714 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153844, d155714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153844, d155714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153854 q = 0) : d155724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153854, d155724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153854, d155724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13916 (p : Pattern) (selected : d153870 p = 0) : d155740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153860 q = 0) : d155730 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153860, d155730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153860, d155730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13879 q selected
  have h2 (q : Pattern) (selected : d153684 q = 0) : d155625 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153684, d155625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13879 q selected
    | true =>
      simp only [d153684, d155625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153861 q = 0) : d155731 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153861, d155731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153861, d155731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153685 q = 0) : d155626 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153685, d155626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153685, d155626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153862 q = 0) : d155732 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153862, d155732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153862, d155732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153863 q = 0) : d155733 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153863, d155733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153863, d155733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153864 q = 0) : d155734 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153864, d155734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153864, d155734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13859 q selected
  have h8 (q : Pattern) (selected : d153588 q = 0) : d155529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153588, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13859 q selected
    | true =>
      simp only [d153588, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153865 q = 0) : d155735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153865, d155735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153865, d155735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153589 q = 0) : d155530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153589, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153589, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153866 q = 0) : d155736 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153866, d155736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153866, d155736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153867 q = 0) : d155737 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153867, d155737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153867, d155737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153868 q = 0) : d155738 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153868, d155738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153868, d155738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153481 q = 0) : d155454 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153481, d155454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153481, d155454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13814 q selected
  have h15 (q : Pattern) (selected : d153354 q = 0) : d155367 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13814 q selected
    | true =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153482 q = 0) : d155455 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153482, d155455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153482, d155455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153355 q = 0) : d155368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153483 q = 0) : d155456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153483, d155456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153483, d155456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153484 q = 0) : d155457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153484, d155457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153484, d155457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153869 q = 0) : d155739 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153869, d155739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153869, d155739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d153870 q = 0) : d155740 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153870, d155740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153870, d155740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro13917 (p : Pattern) (selected : d153876 p = 0) : d155746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153864 q = 0) : d155734 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153864, d155734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153864, d155734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13859 q selected
  have h2 (q : Pattern) (selected : d153588 q = 0) : d155529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153588, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13859 q selected
    | true =>
      simp only [d153588, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153865 q = 0) : d155735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153865, d155735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153865, d155735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153589 q = 0) : d155530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153589, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153589, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153866 q = 0) : d155736 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153866, d155736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153866, d155736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153867 q = 0) : d155737 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153867, d155737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153867, d155737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153871 q = 0) : d155741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153871, d155741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153871, d155741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13860 q selected
  have h8 (q : Pattern) (selected : d153594 q = 0) : d155535 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153594, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13860 q selected
    | true =>
      simp only [d153594, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153872 q = 0) : d155742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153872, d155742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153872, d155742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153595 q = 0) : d155536 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153595, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153595, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153873 q = 0) : d155743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153873, d155743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153873, d155743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153874 q = 0) : d155744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153874, d155744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153874, d155744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153875 q = 0) : d155745 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153875, d155745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153875, d155745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153481 q = 0) : d155454 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153481, d155454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153481, d155454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13814 q selected
  have h15 (q : Pattern) (selected : d153354 q = 0) : d155367 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13814 q selected
    | true =>
      simp only [d153354, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153482 q = 0) : d155455 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153482, d155455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153482, d155455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153355 q = 0) : d155368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153355, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153483 q = 0) : d155456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153483, d155456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153483, d155456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153484 q = 0) : d155457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153484, d155457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153484, d155457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153224 q = 0) : d155256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
  have h21 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d153225 q = 0) : d155257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d153226 q = 0) : d155258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d153227 q = 0) : d155259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d153485 q = 0) : d155458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153485, d155458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153485, d155458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d153876 q = 0) : d155746 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153876, d155746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153876, d155746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro13918 (p : Pattern) (selected : d153886 p = 0) : d155756 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153880 q = 0) : d155750 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153880, d155750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153880, d155750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13881 q selected
  have h2 (q : Pattern) (selected : d153696 q = 0) : d155637 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153696, d155637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13881 q selected
    | true =>
      simp only [d153696, d155637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153881 q = 0) : d155751 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153881, d155751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153881, d155751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153697 q = 0) : d155638 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153697, d155638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153697, d155638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153882 q = 0) : d155752 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153882, d155752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153882, d155752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153883 q = 0) : d155753 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153883, d155753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153883, d155753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153224 q = 0) : d155256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
  have h8 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153225 q = 0) : d155257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153226 q = 0) : d155258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153227 q = 0) : d155259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153884 q = 0) : d155754 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153884, d155754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153884, d155754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153885 q = 0) : d155755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153885, d155755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153885, d155755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153886 q = 0) : d155756 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153886, d155756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153886, d155756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13919 (p : Pattern) (selected : d153896 p = 0) : d155766 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153871 q = 0) : d155741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153871, d155741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153871, d155741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13860 q selected
  have h2 (q : Pattern) (selected : d153594 q = 0) : d155535 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153594, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13860 q selected
    | true =>
      simp only [d153594, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153872 q = 0) : d155742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153872, d155742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153872, d155742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153595 q = 0) : d155536 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153595, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153595, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153873 q = 0) : d155743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153873, d155743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153873, d155743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153874 q = 0) : d155744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153874, d155744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153874, d155744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153891 q = 0) : d155761 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153891, d155761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153891, d155761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13862 q selected
  have h8 (q : Pattern) (selected : d153602 q = 0) : d155543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153602, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13862 q selected
    | true =>
      simp only [d153602, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153892 q = 0) : d155762 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153892, d155762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153892, d155762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153603 q = 0) : d155544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153603, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153603, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153893 q = 0) : d155763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153893, d155763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153893, d155763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153894 q = 0) : d155764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153894, d155764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153894, d155764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153895 q = 0) : d155765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153895, d155765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153895, d155765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153224 q = 0) : d155256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153224, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
  have h15 (q : Pattern) (selected : d153131 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13771 q selected
    | true =>
      simp only [d153131, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153225 q = 0) : d155257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153225, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153132 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153132, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153226 q = 0) : d155258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153226, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153227 q = 0) : d155259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153227, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153885 q = 0) : d155755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153885, d155755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153885, d155755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d153896 q = 0) : d155766 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153896, d155766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153896, d155766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro13920 (p : Pattern) (selected : d153905 p = 0) : d155775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153900 q = 0) : d155770 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153900, d155770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153900, d155770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13864 q selected
  have h2 (q : Pattern) (selected : d153614 q = 0) : d155555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153614, d155555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13864 q selected
    | true =>
      simp only [d153614, d155555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153901 q = 0) : d155771 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153901, d155771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153901, d155771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153615 q = 0) : d155556 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153615, d155556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153615, d155556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153902 q = 0) : d155772 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153902, d155772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153902, d155772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153903 q = 0) : d155773 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153903, d155773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153903, d155773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153904 q = 0) : d155774 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153904, d155774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153904, d155774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153905 q = 0) : d155775 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153905, d155775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153905, d155775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13921 (p : Pattern) (selected : d153911 p = 0) : d155781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153877 q = 0) : d155747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153877, d155747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13916 q selected
    | true =>
      simp only [d153877, d155747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13917 q selected
  have h2 (q : Pattern) (selected : d153878 q = 0) : d155748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153878, d155748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153878, d155748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153879 q = 0) : d155749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153879, d155749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153879, d155749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153887 q = 0) : d155757 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153887, d155757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13917 q selected
    | true =>
      simp only [d153887, d155757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13918 q selected
  have h5 (q : Pattern) (selected : d153888 q = 0) : d155758 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153888, d155758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153888, d155758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153889 q = 0) : d155759 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153889, d155759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153889, d155759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153890 q = 0) : d155760 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153890, d155760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153890, d155760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153897 q = 0) : d155767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153897, d155767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13917 q selected
    | true =>
      simp only [d153897, d155767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13919 q selected
  have h9 (q : Pattern) (selected : d153898 q = 0) : d155768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153898, d155768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153898, d155768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153899 q = 0) : d155769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153899, d155769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153899, d155769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153906 q = 0) : d155776 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153906, d155776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13919 q selected
    | true =>
      simp only [d153906, d155776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13920 q selected
  have h12 (q : Pattern) (selected : d153907 q = 0) : d155777 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153907, d155777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153907, d155777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153908 q = 0) : d155778 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153908, d155778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153908, d155778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153909 q = 0) : d155779 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153909, d155779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153909, d155779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153910 q = 0) : d155780 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153910, d155780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153910, d155780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153911 q = 0) : d155781 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153911, d155781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153911, d155781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13922 (p : Pattern) (selected : d153916 p = 0) : d155786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153897 q = 0) : d155767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153897, d155767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13917 q selected
    | true =>
      simp only [d153897, d155767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13919 q selected
  have h2 (q : Pattern) (selected : d153898 q = 0) : d155768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153898, d155768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153898, d155768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153899 q = 0) : d155769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153899, d155769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153899, d155769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153906 q = 0) : d155776 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153906, d155776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13919 q selected
    | true =>
      simp only [d153906, d155776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13920 q selected
  have h5 (q : Pattern) (selected : d153907 q = 0) : d155777 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153907, d155777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153907, d155777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153908 q = 0) : d155778 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153908, d155778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153908, d155778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153909 q = 0) : d155779 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153909, d155779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153909, d155779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153914 q = 0) : d155784 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153914, d155784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153914, d155784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153915 q = 0) : d155785 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153915, d155785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153915, d155785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153916 q = 0) : d155786 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153916, d155786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153916, d155786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13923 (p : Pattern) (selected : d153922 p = 0) : d155792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153912 q = 0) : d155782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153912, d155782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13921 q selected
    | true =>
      simp only [d153912, d155782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153913 q = 0) : d155783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153913, d155783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153913, d155783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153917 q = 0) : d155787 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153917, d155787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13922 q selected
    | true =>
      simp only [d153917, d155787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153918 q = 0) : d155788 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153918, d155788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153918, d155788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153919 q = 0) : d155789 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153919, d155789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153919, d155789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153920 q = 0) : d155790 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153920, d155790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153920, d155790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153921 q = 0) : d155791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153921, d155791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153921, d155791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153922 q = 0) : d155792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153922, d155792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153922, d155792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13924 (p : Pattern) (selected : d153924 p = 0) : d155794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153891 q = 0) : d155761 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153891, d155761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153891, d155761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13862 q selected
  have h2 (q : Pattern) (selected : d153602 q = 0) : d155543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153602, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13862 q selected
    | true =>
      simp only [d153602, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153892 q = 0) : d155762 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153892, d155762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153892, d155762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153603 q = 0) : d155544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153603, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153603, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153893 q = 0) : d155763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153893, d155763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153893, d155763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153894 q = 0) : d155764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153894, d155764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153894, d155764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153923 q = 0) : d155793 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153923, d155793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153923, d155793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153924 q = 0) : d155794 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153924, d155794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153924, d155794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13925 (p : Pattern) (selected : d153930 p = 0) : d155800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153925 q = 0) : d155795 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153925, d155795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13919 q selected
    | true =>
      simp only [d153925, d155795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13924 q selected
  have h2 (q : Pattern) (selected : d153926 q = 0) : d155796 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153926, d155796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153926, d155796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153927 q = 0) : d155797 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153927, d155797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153927, d155797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153928 q = 0) : d155798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153928, d155798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153928, d155798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153929 q = 0) : d155799 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153929, d155799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153929, d155799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153930 q = 0) : d155800 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153930, d155800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153930, d155800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13926 (p : Pattern) (selected : d153936 p = 0) : d155806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153917 q = 0) : d155787 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153917, d155787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13922 q selected
    | true =>
      simp only [d153917, d155787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153918 q = 0) : d155788 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153918, d155788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153918, d155788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153931 q = 0) : d155801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153931, d155801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13925 q selected
    | true =>
      simp only [d153931, d155801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153932 q = 0) : d155802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153932, d155802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153932, d155802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153933 q = 0) : d155803 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153933, d155803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153933, d155803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153934 q = 0) : d155804 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153934, d155804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153934, d155804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153935 q = 0) : d155805 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153935, d155805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153935, d155805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153936 q = 0) : d155806 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153936, d155806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153936, d155806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13927 (p : Pattern) (selected : d153952 p = 0) : d155746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153938 q = 0) : d155734 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153938, d155734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153938, d155734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13887 q selected
  have h2 (q : Pattern) (selected : d153726 q = 0) : d155529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153726, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13887 q selected
    | true =>
      simp only [d153726, d155529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153939 q = 0) : d155735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153939, d155735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153939, d155735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153727 q = 0) : d155530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153727, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153727, d155530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153940 q = 0) : d155736 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153940, d155736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153940, d155736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153941 q = 0) : d155737 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153941, d155737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153941, d155737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153942 q = 0) : d155741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153942, d155741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153942, d155741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13888 q selected
  have h8 (q : Pattern) (selected : d153732 q = 0) : d155535 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153732, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13888 q selected
    | true =>
      simp only [d153732, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153943 q = 0) : d155742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153943, d155742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153943, d155742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153733 q = 0) : d155536 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153733, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153733, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153944 q = 0) : d155743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153944, d155743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153944, d155743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153945 q = 0) : d155744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153945, d155744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153945, d155744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153946 q = 0) : d155745 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153946, d155745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153946, d155745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153947 q = 0) : d155454 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153947, d155454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153947, d155454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13889 q selected
  have h15 (q : Pattern) (selected : d153739 q = 0) : d155367 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153739, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13889 q selected
    | true =>
      simp only [d153739, d155367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153948 q = 0) : d155455 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153948, d155455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153948, d155455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153740 q = 0) : d155368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153740, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153740, d155368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153949 q = 0) : d155456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153949, d155456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153949, d155456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153950 q = 0) : d155457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153950, d155457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153950, d155457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153522 q = 0) : d155256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153522, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153522, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13820 q selected
  have h21 (q : Pattern) (selected : d153386 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13820 q selected
    | true =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d153523 q = 0) : d155257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153523, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d153523, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d153387 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d153524 q = 0) : d155258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153524, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d153524, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d153525 q = 0) : d155259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153525, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d153525, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d153951 q = 0) : d155458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153951, d155458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153951, d155458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d153952 q = 0) : d155746 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153952, d155746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153952, d155746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro13928 (p : Pattern) (selected : d153959 p = 0) : d155766 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153942 q = 0) : d155741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153942, d155741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153942, d155741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13888 q selected
  have h2 (q : Pattern) (selected : d153732 q = 0) : d155535 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153732, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13888 q selected
    | true =>
      simp only [d153732, d155535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153943 q = 0) : d155742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153943, d155742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153943, d155742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153733 q = 0) : d155536 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153733, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153733, d155536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153944 q = 0) : d155743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153944, d155743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153944, d155743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153945 q = 0) : d155744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153945, d155744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153945, d155744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153953 q = 0) : d155761 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153953, d155761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153953, d155761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13891 q selected
  have h8 (q : Pattern) (selected : d153747 q = 0) : d155543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153747, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13891 q selected
    | true =>
      simp only [d153747, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d153954 q = 0) : d155762 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153954, d155762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153954, d155762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153748 q = 0) : d155544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153748, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153748, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d153955 q = 0) : d155763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153955, d155763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d153955, d155763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d153956 q = 0) : d155764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153956, d155764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153956, d155764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153957 q = 0) : d155765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153957, d155765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153957, d155765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153522 q = 0) : d155256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153522, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153522, d155256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13820 q selected
  have h15 (q : Pattern) (selected : d153386 q = 0) : d155186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13820 q selected
    | true =>
      simp only [d153386, d155186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153523 q = 0) : d155257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153523, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153523, d155257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d153387 q = 0) : d155187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d153387, d155187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d153524 q = 0) : d155258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153524, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d153524, d155258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d153525 q = 0) : d155259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153525, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d153525, d155259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d153958 q = 0) : d155755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153958, d155755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d153958, d155755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d153959 q = 0) : d155766 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153959, d155766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153959, d155766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro13929 (p : Pattern) (selected : d153968 p = 0) : d155775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153963 q = 0) : d155770 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153963, d155770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153963, d155770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13893 q selected
  have h2 (q : Pattern) (selected : d153759 q = 0) : d155555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153759, d155555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13893 q selected
    | true =>
      simp only [d153759, d155555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153964 q = 0) : d155771 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153964, d155771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153964, d155771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153760 q = 0) : d155556 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153760, d155556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153760, d155556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153965 q = 0) : d155772 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153965, d155772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153965, d155772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153966 q = 0) : d155773 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153966, d155773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153966, d155773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153967 q = 0) : d155774 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153967, d155774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153967, d155774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153968 q = 0) : d155775 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153968, d155775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153968, d155775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13930 (p : Pattern) (selected : d153974 p = 0) : d155794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153953 q = 0) : d155761 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153953, d155761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153953, d155761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13891 q selected
  have h2 (q : Pattern) (selected : d153747 q = 0) : d155543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153747, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13891 q selected
    | true =>
      simp only [d153747, d155543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153954 q = 0) : d155762 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153954, d155762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153954, d155762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153748 q = 0) : d155544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153748, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153748, d155544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153955 q = 0) : d155763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153955, d155763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153955, d155763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153956 q = 0) : d155764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153956, d155764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153956, d155764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153973 q = 0) : d155793 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d153973, d155793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153973, d155793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153974 q = 0) : d155794 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d153974, d155794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153974, d155794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13931 (p : Pattern) (selected : d153980 p = 0) : d155809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153960 q = 0) : d155767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153960, d155767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13927 q selected
    | true =>
      simp only [d153960, d155767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13928 q selected
  have h2 (q : Pattern) (selected : d153961 q = 0) : d155768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153961, d155768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153961, d155768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153962 q = 0) : d155769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153962, d155769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153962, d155769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153969 q = 0) : d155776 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153969, d155776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13928 q selected
    | true =>
      simp only [d153969, d155776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13929 q selected
  have h5 (q : Pattern) (selected : d153970 q = 0) : d155777 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153970, d155777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153970, d155777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153971 q = 0) : d155778 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153971, d155778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153971, d155778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153972 q = 0) : d155779 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153972, d155779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153972, d155779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153975 q = 0) : d155795 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153975, d155795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13928 q selected
    | true =>
      simp only [d153975, d155795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13930 q selected
  have h9 (q : Pattern) (selected : d153976 q = 0) : d155796 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153976, d155796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153976, d155796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153977 q = 0) : d155797 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153977, d155797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153977, d155797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153978 q = 0) : d155798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153978, d155798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153978, d155798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153979 q = 0) : d155808 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153979, d155808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153979, d155808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153980 q = 0) : d155809 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153980, d155809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153980, d155809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13932 (p : Pattern) (selected : d153984 p = 0) : d155800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153975 q = 0) : d155795 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153975, d155795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13928 q selected
    | true =>
      simp only [d153975, d155795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13930 q selected
  have h2 (q : Pattern) (selected : d153976 q = 0) : d155796 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153976, d155796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153976, d155796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153977 q = 0) : d155797 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153977, d155797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153977, d155797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153978 q = 0) : d155798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153978, d155798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153978, d155798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153983 q = 0) : d155799 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153983, d155799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153983, d155799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153984 q = 0) : d155800 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153984, d155800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153984, d155800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13933 (p : Pattern) (selected : d153990 p = 0) : d155815 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153981 q = 0) : d155810 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153981, d155810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13931 q selected
    | true =>
      simp only [d153981, d155810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153982 q = 0) : d155811 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153982, d155811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153982, d155811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153985 q = 0) : d155801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153985, d155801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13932 q selected
    | true =>
      simp only [d153985, d155801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153986 q = 0) : d155802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153986, d155802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153986, d155802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153987 q = 0) : d155812 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153987, d155812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153987, d155812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153988 q = 0) : d155813 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153988, d155813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153988, d155813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d153989 q = 0) : d155814 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153989, d155814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153989, d155814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d153990 q = 0) : d155815 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153990, d155815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153990, d155815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13934 (p : Pattern) (selected : d153994 p = 0) : d155819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153985 q = 0) : d155801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153985, d155801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13932 q selected
    | true =>
      simp only [d153985, d155801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153986 q = 0) : d155802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153986, d155802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153986, d155802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153991 q = 0) : d155816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153991, d155816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153991, d155816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153992 q = 0) : d155817 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d153992, d155817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153992, d155817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153993 q = 0) : d155818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153993, d155818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153993, d155818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153994 q = 0) : d155819 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153994, d155819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153994, d155819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13935 (p : Pattern) (selected : d153998 p = 0) : d155809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153897 q = 0) : d155767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153897, d155767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13917 q selected
    | true =>
      simp only [d153897, d155767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13919 q selected
  have h2 (q : Pattern) (selected : d153898 q = 0) : d155768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153898, d155768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153898, d155768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153899 q = 0) : d155769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153899, d155769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153899, d155769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153906 q = 0) : d155776 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153906, d155776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13919 q selected
    | true =>
      simp only [d153906, d155776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13920 q selected
  have h5 (q : Pattern) (selected : d153907 q = 0) : d155777 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153907, d155777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153907, d155777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153908 q = 0) : d155778 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153908, d155778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153908, d155778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153909 q = 0) : d155779 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153909, d155779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153909, d155779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d153925 q = 0) : d155795 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153925, d155795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13919 q selected
    | true =>
      simp only [d153925, d155795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13924 q selected
  have h9 (q : Pattern) (selected : d153926 q = 0) : d155796 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153926, d155796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153926, d155796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d153927 q = 0) : d155797 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153927, d155797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153927, d155797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153928 q = 0) : d155798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153928, d155798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153928, d155798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153997 q = 0) : d155808 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d153997, d155808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153997, d155808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d153998 q = 0) : d155809 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d153998, d155809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d153998, d155809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13936 (p : Pattern) (selected : d154004 p = 0) : d155825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153999 q = 0) : d155810 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153999, d155810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13935 q selected
    | true =>
      simp only [d153999, d155810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154000 q = 0) : d155811 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154000, d155811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154000, d155811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154001 q = 0) : d155822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154001, d155822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154001, d155822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154002 q = 0) : d155823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154002, d155823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154002, d155823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154003 q = 0) : d155824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154003, d155824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154003, d155824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154004 q = 0) : d155825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154004, d155825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154004, d155825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13937 (p : Pattern) (selected : d154010 p = 0) : d155831 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153937 q = 0) : d155807 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153937, d155807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13923 q selected
    | true =>
      simp only [d153937, d155807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13926 q selected
  have h2 (q : Pattern) (selected : d153995 q = 0) : d155820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153995, d155820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13933 q selected
    | true =>
      simp only [d153995, d155820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13934 q selected
  have h3 (q : Pattern) (selected : d153996 q = 0) : d155821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153996, d155821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153996, d155821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154005 q = 0) : d155826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154005, d155826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13936 q selected
    | true =>
      simp only [d154005, d155826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154006 q = 0) : d155827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154006, d155827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154006, d155827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154007 q = 0) : d155828 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154007, d155828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154007, d155828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154008 q = 0) : d155829 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154008, d155829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154008, d155829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154009 q = 0) : d155830 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154009, d155830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154009, d155830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154010 q = 0) : d155831 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154010, d155831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154010, d155831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13938 (p : Pattern) (selected : d154015 p = 0) : d155819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153931 q = 0) : d155801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153931, d155801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13925 q selected
    | true =>
      simp only [d153931, d155801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153932 q = 0) : d155802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153932, d155802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153932, d155802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154012 q = 0) : d155816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154012, d155816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154012, d155816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154013 q = 0) : d155817 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154013, d155817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154013, d155817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154014 q = 0) : d155818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154014, d155818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154014, d155818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154015 q = 0) : d155819 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154015, d155819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154015, d155819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13939 (p : Pattern) (selected : d154021 p = 0) : d155838 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154016 q = 0) : d155833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154016, d155833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13938 q selected
    | true =>
      simp only [d154016, d155833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154017 q = 0) : d155834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154017, d155834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154017, d155834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154018 q = 0) : d155835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154018, d155835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154018, d155835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154019 q = 0) : d155836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154019, d155836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154019, d155836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154020 q = 0) : d155837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154020, d155837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154020, d155837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154021 q = 0) : d155838 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154021, d155838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154021, d155838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13940 (p : Pattern) (selected : d154027 p = 0) : d155844 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153652 q = 0) : d155593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153652, d155593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153652, d155593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13871 q selected
  have h2 (q : Pattern) (selected : d153653 q = 0) : d155594 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153653, d155594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153653, d155594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153662 q = 0) : d155603 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153662, d155603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13871 q selected
    | true =>
      simp only [d153662, d155603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13874 q selected
  have h4 (q : Pattern) (selected : d153663 q = 0) : d155604 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153663, d155604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153663, d155604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153664 q = 0) : d155605 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153664, d155605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153664, d155605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153828 q = 0) : d155698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153828, d155698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13901 q selected
    | true =>
      simp only [d153828, d155698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13911 q selected
  have h7 (q : Pattern) (selected : d153846 q = 0) : d155716 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153846, d155716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13912 q selected
    | true =>
      simp only [d153846, d155716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13913 q selected
  have h8 (q : Pattern) (selected : d153847 q = 0) : d155717 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153847, d155717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153847, d155717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153848 q = 0) : d155718 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153848, d155718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153848, d155718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d153849 q = 0) : d155719 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153849, d155719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153849, d155719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153853 q = 0) : d155723 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153853, d155723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153853, d155723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13914 q selected
  have h12 (q : Pattern) (selected : d153855 q = 0) : d155725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153855, d155725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153855, d155725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13915 q selected
  have h13 (q : Pattern) (selected : d153856 q = 0) : d155726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153856, d155726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153856, d155726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153857 q = 0) : d155727 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153857, d155727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d153857, d155727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d153858 q = 0) : d155728 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d153858, d155728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d153858, d155728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d153859 q = 0) : d155729 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d153859, d155729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153859, d155729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154011 q = 0) : d155832 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154011, d155832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154011, d155832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13937 q selected
  have h18 (q : Pattern) (selected : d154022 q = 0) : d155839 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154022, d155839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154022, d155839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13939 q selected
  have h19 (q : Pattern) (selected : d154023 q = 0) : d155840 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154023, d155840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d154023, d155840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d154024 q = 0) : d155841 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154024, d155841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d154024, d155841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d154025 q = 0) : d155842 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154025, d155842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d154025, d155842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d154026 q = 0) : d155843 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154026, d155843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d154026, d155843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d154027 q = 0) : d155844 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d154027, d155844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154027, d155844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro13941 (p : Pattern) (selected : d154033 p = 0) : d155850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154028 q = 0) : d155845 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d154028, d155845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154028, d155845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13940 q selected
  have h2 (q : Pattern) (selected : d154029 q = 0) : d155846 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d154029, d155846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154029, d155846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154030 q = 0) : d155847 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d154030, d155847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154030, d155847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154031 q = 0) : d155848 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d154031, d155848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154031, d155848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154032 q = 0) : d155849 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d154032, d155849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154032, d155849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154033 q = 0) : d155850 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d154033, d155850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154033, d155850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13942 (p : Pattern) (selected : d154038 p = 0) : d155855 p = 1 := by
  have h0 (q : Pattern) (selected : d1527 q = 0) : d52968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro460 q selected
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro461 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1528 q = 0) : d52969 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h3 (q : Pattern) (selected : d1529 q = 0) : d52970 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1534 q = 0) : d52975 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro462 q selected
    | true =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1535 q = 0) : d52976 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154037 q = 0) : d155854 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154037, d155854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154037, d155854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154038 q = 0) : d155855 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154038, d155855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154038, d155855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro13943 (p : Pattern) (selected : d154044 p = 0) : d155861 p = 1 := by
  have h0 (q : Pattern) (selected : d1543 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro463 q selected
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro464 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1544 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h3 (q : Pattern) (selected : d1545 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1549 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1550 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154043 q = 0) : d155860 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154043, d155860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154043, d155860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154044 q = 0) : d155861 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154044, d155861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154044, d155861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro13944 (p : Pattern) (selected : d154051 p = 0) : d155868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10057 q = 0) : d101484 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2813 q selected
    | true =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10058 q = 0) : d101485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154050 q = 0) : d155867 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154050, d155867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154050, d155867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154051 q = 0) : d155868 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154051, d155868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154051, d155868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro13945 (p : Pattern) (selected : d154057 p = 0) : d155874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154039 q = 0) : d155856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154039, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13942 q selected
    | true =>
      simp only [d154039, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154040 q = 0) : d155857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154040, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154040, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154041 q = 0) : d155858 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154041, d155858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154041, d155858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154042 q = 0) : d155859 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154042, d155859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154042, d155859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154045 q = 0) : d155862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154045, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13943 q selected
    | true =>
      simp only [d154045, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154046 q = 0) : d155863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154046, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154046, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154047 q = 0) : d155864 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154047, d155864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154047, d155864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154048 q = 0) : d155865 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154048, d155865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154048, d155865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154049 q = 0) : d155866 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154049, d155866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154049, d155866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154052 q = 0) : d155869 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13944 q selected
    | true =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154053 q = 0) : d155870 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154054 q = 0) : d155871 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154054, d155871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154054, d155871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154055 q = 0) : d155872 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154055, d155872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154055, d155872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d154056 q = 0) : d155873 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154056, d155873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154056, d155873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154057 q = 0) : d155874 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154057, d155874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154057, d155874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13946 (p : Pattern) (selected : d154059 p = 0) : d155876 p = 1 := by
  have h0 (q : Pattern) (selected : d1560 q = 0) : d53001 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1560, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1560, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1115 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h3 (q : Pattern) (selected : d1561 q = 0) : d53002 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1561, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1561, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1564 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1565 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154058 q = 0) : d155875 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154058, d155875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154058, d155875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154059 q = 0) : d155876 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154059, d155876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154059, d155876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro13947 (p : Pattern) (selected : d154066 p = 0) : d155883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154045 q = 0) : d155862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154045, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13943 q selected
    | true =>
      simp only [d154045, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154046 q = 0) : d155863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154046, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154046, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154047 q = 0) : d155864 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154047, d155864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154047, d155864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154048 q = 0) : d155865 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154048, d155865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154048, d155865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154060 q = 0) : d155877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154060, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13946 q selected
    | true =>
      simp only [d154060, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154061 q = 0) : d155878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154061, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154061, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154062 q = 0) : d155879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154062, d155879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154062, d155879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154063 q = 0) : d155880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154063, d155880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154063, d155880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154064 q = 0) : d155881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154064, d155881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154064, d155881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154052 q = 0) : d155869 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13944 q selected
    | true =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154053 q = 0) : d155870 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154054 q = 0) : d155871 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154054, d155871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154054, d155871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154055 q = 0) : d155872 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154055, d155872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154055, d155872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d154065 q = 0) : d155882 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154065, d155882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154065, d155882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d154066 q = 0) : d155883 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154066, d155883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154066, d155883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13948 (p : Pattern) (selected : d154071 p = 0) : d155888 p = 1 := by
  have h0 (q : Pattern) (selected : d5123 q = 0) : d69210 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5123, d69210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2813 q selected
    | true =>
      simp only [d5123, d69210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d5124 q = 0) : d69211 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5124, d69211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5124, d69211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1564 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d1565 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d154070 q = 0) : d155887 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154070, d155887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154070, d155887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154071 q = 0) : d155888 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154071, d155888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154071, d155888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro13949 (p : Pattern) (selected : d154077 p = 0) : d155894 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154072 q = 0) : d155889 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154072, d155889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13948 q selected
    | true =>
      simp only [d154072, d155889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154073 q = 0) : d155890 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154073, d155890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154073, d155890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154074 q = 0) : d155891 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154074, d155891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154074, d155891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154075 q = 0) : d155892 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154075, d155892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154075, d155892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154076 q = 0) : d155893 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154076, d155893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154076, d155893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154077 q = 0) : d155894 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154077, d155894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154077, d155894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13950 (p : Pattern) (selected : d154083 p = 0) : d155900 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154060 q = 0) : d155877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154060, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13946 q selected
    | true =>
      simp only [d154060, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154061 q = 0) : d155878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154061, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154061, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154062 q = 0) : d155879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154062, d155879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154062, d155879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154063 q = 0) : d155880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154063, d155880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154063, d155880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154082 q = 0) : d155899 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154082, d155899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154082, d155899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154083 q = 0) : d155900 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154083, d155900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154083, d155900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13951 (p : Pattern) (selected : d154089 p = 0) : d155906 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154067 q = 0) : d155884 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154067, d155884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13945 q selected
    | true =>
      simp only [d154067, d155884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13947 q selected
  have h2 (q : Pattern) (selected : d154068 q = 0) : d155885 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154068, d155885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154068, d155885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154069 q = 0) : d155886 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154069, d155886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154069, d155886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154078 q = 0) : d155895 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154078, d155895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13947 q selected
    | true =>
      simp only [d154078, d155895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13949 q selected
  have h5 (q : Pattern) (selected : d154079 q = 0) : d155896 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154079, d155896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154079, d155896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154080 q = 0) : d155897 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154080, d155897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154080, d155897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154081 q = 0) : d155898 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154081, d155898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154081, d155898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154084 q = 0) : d155901 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154084, d155901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13947 q selected
    | true =>
      simp only [d154084, d155901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13950 q selected
  have h9 (q : Pattern) (selected : d154085 q = 0) : d155902 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154085, d155902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154085, d155902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154086 q = 0) : d155903 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154086, d155903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154086, d155903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154087 q = 0) : d155904 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154087, d155904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154087, d155904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154088 q = 0) : d155905 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154088, d155905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154088, d155905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154089 q = 0) : d155906 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154089, d155906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154089, d155906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13952 (p : Pattern) (selected : d154093 p = 0) : d155910 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154084 q = 0) : d155901 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154084, d155901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13947 q selected
    | true =>
      simp only [d154084, d155901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13950 q selected
  have h2 (q : Pattern) (selected : d154085 q = 0) : d155902 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154085, d155902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154085, d155902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154086 q = 0) : d155903 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154086, d155903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154086, d155903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154087 q = 0) : d155904 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154087, d155904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154087, d155904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154092 q = 0) : d155909 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154092, d155909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154092, d155909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154093 q = 0) : d155910 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154093, d155910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154093, d155910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13953 (p : Pattern) (selected : d154099 p = 0) : d155916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154090 q = 0) : d155907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13951 q selected
    | true =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154091 q = 0) : d155908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154096 q = 0) : d155913 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154097 q = 0) : d155914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154097, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154097, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154098 q = 0) : d155915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154098, d155915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154098, d155915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154099 q = 0) : d155916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154099, d155916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154099, d155916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13954 (p : Pattern) (selected : d154103 p = 0) : d155920 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154100 q = 0) : d155917 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154101 q = 0) : d155918 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154101, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154101, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154102 q = 0) : d155919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154102, d155919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154102, d155919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154103 q = 0) : d155920 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154103, d155920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154103, d155920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13955 (p : Pattern) (selected : d154109 p = 0) : d155926 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154104 q = 0) : d155921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154104, d155921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13953 q selected
    | true =>
      simp only [d154104, d155921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13954 q selected
  have h2 (q : Pattern) (selected : d154105 q = 0) : d155922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154105, d155922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154105, d155922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154106 q = 0) : d155923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154106, d155923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154106, d155923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154107 q = 0) : d155924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154107, d155924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154107, d155924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154108 q = 0) : d155925 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154108, d155925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154108, d155925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154109 q = 0) : d155926 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154109, d155926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154109, d155926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13956 (p : Pattern) (selected : d154112 p = 0) : d155929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154090 q = 0) : d155907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13951 q selected
    | true =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154091 q = 0) : d155908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154096 q = 0) : d155913 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154097 q = 0) : d155914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154097, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154097, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154098 q = 0) : d155915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154098, d155915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154098, d155915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154112 q = 0) : d155929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154112, d155929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154112, d155929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13957 (p : Pattern) (selected : d154113 p = 0) : d155930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154100 q = 0) : d155917 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154101 q = 0) : d155918 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154101, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154101, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154102 q = 0) : d155919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154102, d155919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154102, d155919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154113 q = 0) : d155930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154113, d155930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154113, d155930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13958 (p : Pattern) (selected : d154119 p = 0) : d155936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154104 q = 0) : d155921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154104, d155921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13953 q selected
    | true =>
      simp only [d154104, d155921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13954 q selected
  have h2 (q : Pattern) (selected : d154105 q = 0) : d155922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154105, d155922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154105, d155922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154106 q = 0) : d155923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154106, d155923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154106, d155923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154107 q = 0) : d155924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154107, d155924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154107, d155924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154108 q = 0) : d155925 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154108, d155925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154108, d155925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154114 q = 0) : d155931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154114, d155931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13956 q selected
    | true =>
      simp only [d154114, d155931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13957 q selected
  have h7 (q : Pattern) (selected : d154115 q = 0) : d155932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154115, d155932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154115, d155932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154116 q = 0) : d155933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154116, d155933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154116, d155933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154117 q = 0) : d155934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154117, d155934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154117, d155934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154118 q = 0) : d155935 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154118, d155935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154118, d155935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154119 q = 0) : d155936 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154119, d155936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154119, d155936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13959 (p : Pattern) (selected : d154124 p = 0) : d155941 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154090 q = 0) : d155907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13951 q selected
    | true =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154091 q = 0) : d155908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154096 q = 0) : d155913 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154097 q = 0) : d155914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154097, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154097, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154123 q = 0) : d155940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154123, d155940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154123, d155940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154124 q = 0) : d155941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154124, d155941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154124, d155941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13960 (p : Pattern) (selected : d154126 p = 0) : d155943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154100 q = 0) : d155917 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154101 q = 0) : d155918 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154101, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154101, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154125 q = 0) : d155942 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154125, d155942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154125, d155942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154126 q = 0) : d155943 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154126, d155943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154126, d155943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13961 (p : Pattern) (selected : d154133 p = 0) : d155950 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154090 q = 0) : d155907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13951 q selected
    | true =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154091 q = 0) : d155908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154096 q = 0) : d155913 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154131 q = 0) : d155948 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154131, d155948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154131, d155948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154132 q = 0) : d155949 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154132, d155949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154132, d155949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154133 q = 0) : d155950 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154133, d155950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154133, d155950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13962 (p : Pattern) (selected : d154136 p = 0) : d155953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154100 q = 0) : d155917 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154134 q = 0) : d155951 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154134, d155951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154134, d155951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154135 q = 0) : d155952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154135, d155952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154135, d155952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154136 q = 0) : d155953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154136, d155953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154136, d155953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13963 (p : Pattern) (selected : d154141 p = 0) : d155958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1200 q = 0) : d52781 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro405 q selected
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1201 q = 0) : d52782 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1204 q = 0) : d52785 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro406 q selected
    | true =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1205 q = 0) : d52786 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154140 q = 0) : d155957 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154140, d155957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154140, d155957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154141 q = 0) : d155958 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154141, d155958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154141, d155958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13964 (p : Pattern) (selected : d154147 p = 0) : d155964 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154142 q = 0) : d155959 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154142, d155959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13963 q selected
    | true =>
      simp only [d154142, d155959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154143 q = 0) : d155960 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154143, d155960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154143, d155960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154144 q = 0) : d155961 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154144, d155961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154144, d155961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154145 q = 0) : d155962 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154145, d155962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154145, d155962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154039 q = 0) : d155856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154039, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13942 q selected
    | true =>
      simp only [d154039, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154040 q = 0) : d155857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154040, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154040, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154041 q = 0) : d155858 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154041, d155858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154041, d155858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154042 q = 0) : d155859 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154042, d155859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154042, d155859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154146 q = 0) : d155963 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154146, d155963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154146, d155963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154147 q = 0) : d155964 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154147, d155964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154147, d155964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13965 (p : Pattern) (selected : d154152 p = 0) : d155969 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10055 q = 0) : d101482 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6713 q selected
  have h2 (q : Pattern) (selected : d10056 q = 0) : d101483 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154151 q = 0) : d155968 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154151, d155968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154151, d155968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154152 q = 0) : d155969 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154152, d155969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154152, d155969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro13966 (p : Pattern) (selected : d154158 p = 0) : d155975 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154153 q = 0) : d155970 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154153, d155970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13965 q selected
    | true =>
      simp only [d154153, d155970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154154 q = 0) : d155971 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154154, d155971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154154, d155971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154155 q = 0) : d155972 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154155, d155972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154155, d155972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154156 q = 0) : d155973 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154156, d155973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154156, d155973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154052 q = 0) : d155869 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13944 q selected
    | true =>
      simp only [d154052, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154053 q = 0) : d155870 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154053, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154054 q = 0) : d155871 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154054, d155871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154054, d155871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154055 q = 0) : d155872 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154055, d155872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154055, d155872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154157 q = 0) : d155974 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154157, d155974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154157, d155974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154065 q = 0) : d155882 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154065, d155882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154065, d155882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154158 q = 0) : d155975 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154158, d155975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154158, d155975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13967 (p : Pattern) (selected : d154164 p = 0) : d155981 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154148 q = 0) : d155965 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154148, d155965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13964 q selected
    | true =>
      simp only [d154148, d155965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13945 q selected
  have h2 (q : Pattern) (selected : d154149 q = 0) : d155966 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154149, d155966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154149, d155966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154150 q = 0) : d155967 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154150, d155967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154150, d155967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154159 q = 0) : d155976 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154159, d155976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13945 q selected
    | true =>
      simp only [d154159, d155976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13966 q selected
  have h5 (q : Pattern) (selected : d154160 q = 0) : d155977 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154160, d155977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154160, d155977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154161 q = 0) : d155978 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154161, d155978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154161, d155978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154162 q = 0) : d155979 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154162, d155979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154162, d155979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154067 q = 0) : d155884 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154067, d155884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13945 q selected
    | true =>
      simp only [d154067, d155884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13947 q selected
  have h9 (q : Pattern) (selected : d154068 q = 0) : d155885 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154068, d155885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154068, d155885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154069 q = 0) : d155886 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154069, d155886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154069, d155886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154078 q = 0) : d155895 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154078, d155895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13947 q selected
    | true =>
      simp only [d154078, d155895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13949 q selected
  have h12 (q : Pattern) (selected : d154079 q = 0) : d155896 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154079, d155896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154079, d155896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154080 q = 0) : d155897 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154080, d155897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154080, d155897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154081 q = 0) : d155898 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154081, d155898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154081, d155898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154163 q = 0) : d155980 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154163, d155980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154163, d155980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154164 q = 0) : d155981 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154164, d155981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154164, d155981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13968 (p : Pattern) (selected : d154169 p = 0) : d155986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154067 q = 0) : d155884 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154067, d155884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13945 q selected
    | true =>
      simp only [d154067, d155884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13947 q selected
  have h2 (q : Pattern) (selected : d154068 q = 0) : d155885 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154068, d155885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154068, d155885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154069 q = 0) : d155886 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154069, d155886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154069, d155886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154078 q = 0) : d155895 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154078, d155895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13947 q selected
    | true =>
      simp only [d154078, d155895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13949 q selected
  have h5 (q : Pattern) (selected : d154079 q = 0) : d155896 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154079, d155896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154079, d155896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154080 q = 0) : d155897 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154080, d155897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154080, d155897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154081 q = 0) : d155898 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154081, d155898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154081, d155898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154167 q = 0) : d155984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154167, d155984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154167, d155984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154168 q = 0) : d155985 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154168, d155985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154168, d155985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154169 q = 0) : d155986 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154169, d155986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154169, d155986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13969 (p : Pattern) (selected : d154175 p = 0) : d155992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154165 q = 0) : d155982 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154165, d155982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13967 q selected
    | true =>
      simp only [d154165, d155982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154166 q = 0) : d155983 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154166, d155983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154166, d155983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154170 q = 0) : d155987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154170, d155987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13968 q selected
    | true =>
      simp only [d154170, d155987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154171 q = 0) : d155988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154171, d155988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154171, d155988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154172 q = 0) : d155989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154172, d155989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154172, d155989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154173 q = 0) : d155990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154173, d155990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154173, d155990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154174 q = 0) : d155991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154174, d155991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154174, d155991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154175 q = 0) : d155992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154175, d155992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154175, d155992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13970 (p : Pattern) (selected : d154179 p = 0) : d155996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154170 q = 0) : d155987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154170, d155987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13968 q selected
    | true =>
      simp only [d154170, d155987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154171 q = 0) : d155988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154171, d155988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154171, d155988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154176 q = 0) : d155993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154176, d155993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154176, d155993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154177 q = 0) : d155994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154177, d155994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154177, d155994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154178 q = 0) : d155995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154178, d155995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154178, d155995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154179 q = 0) : d155996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154179, d155996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154179, d155996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13971 (p : Pattern) (selected : d154182 p = 0) : d155855 p = 1 := by
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
  have h4 (q : Pattern) (selected : d1705 q = 0) : d52975 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1705, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro495 q selected
    | true =>
      simp only [d1705, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1706 q = 0) : d52976 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1706, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1706, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154181 q = 0) : d155854 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154181, d155854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154181, d155854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154182 q = 0) : d155855 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154182, d155855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154182, d155855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro13972 (p : Pattern) (selected : d154188 p = 0) : d155861 p = 1 := by
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
  have h4 (q : Pattern) (selected : d1720 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1721 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154187 q = 0) : d155860 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154187, d155860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154187, d155860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154188 q = 0) : d155861 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154188, d155861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154188, d155861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro13973 (p : Pattern) (selected : d154195 p = 0) : d155868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10184 q = 0) : d101484 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10184, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6732 q selected
    | true =>
      simp only [d10184, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10185 q = 0) : d101485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10185, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10185, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154194 q = 0) : d155867 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154194, d155867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154194, d155867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154195 q = 0) : d155868 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154195, d155868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154195, d155868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro13974 (p : Pattern) (selected : d154201 p = 0) : d155874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154183 q = 0) : d155856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154183, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13971 q selected
    | true =>
      simp only [d154183, d155856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154184 q = 0) : d155857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154184, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154184, d155857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154185 q = 0) : d155858 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154185, d155858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154185, d155858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154186 q = 0) : d155859 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154186, d155859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154186, d155859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154189 q = 0) : d155862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154189, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13972 q selected
    | true =>
      simp only [d154189, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154190 q = 0) : d155863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154190, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154190, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154191 q = 0) : d155864 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154191, d155864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154191, d155864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154192 q = 0) : d155865 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154192, d155865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154192, d155865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154193 q = 0) : d155866 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154193, d155866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154193, d155866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154196 q = 0) : d155869 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154196, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13973 q selected
    | true =>
      simp only [d154196, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154197 q = 0) : d155870 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154197, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154197, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154198 q = 0) : d155871 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154198, d155871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154198, d155871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154199 q = 0) : d155872 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154199, d155872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154199, d155872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d154200 q = 0) : d155873 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154200, d155873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154200, d155873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154201 q = 0) : d155874 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154201, d155874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154201, d155874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13975 (p : Pattern) (selected : d154203 p = 0) : d155876 p = 1 := by
  have h0 (q : Pattern) (selected : d1731 q = 0) : d53001 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1731, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1731, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h3 (q : Pattern) (selected : d1732 q = 0) : d53002 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1732, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1732, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1735 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
    | true =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1736 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d154202 q = 0) : d155875 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154202, d155875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154202, d155875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154203 q = 0) : d155876 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154203, d155876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154203, d155876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro13976 (p : Pattern) (selected : d154210 p = 0) : d155883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154189 q = 0) : d155862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154189, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13972 q selected
    | true =>
      simp only [d154189, d155862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154190 q = 0) : d155863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154190, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154190, d155863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154191 q = 0) : d155864 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154191, d155864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154191, d155864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154192 q = 0) : d155865 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154192, d155865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154192, d155865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154204 q = 0) : d155877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154204, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13975 q selected
    | true =>
      simp only [d154204, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154205 q = 0) : d155878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154205, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154205, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154206 q = 0) : d155879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154206, d155879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154206, d155879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154207 q = 0) : d155880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154207, d155880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154207, d155880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154208 q = 0) : d155881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154208, d155881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154208, d155881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154196 q = 0) : d155869 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154196, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13973 q selected
    | true =>
      simp only [d154196, d155869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154197 q = 0) : d155870 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154197, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154197, d155870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154198 q = 0) : d155871 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154198, d155871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154198, d155871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154199 q = 0) : d155872 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154199, d155872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154199, d155872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d154209 q = 0) : d155882 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154209, d155882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154209, d155882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d154210 q = 0) : d155883 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154210, d155883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d154210, d155883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13977 (p : Pattern) (selected : d154215 p = 0) : d155888 p = 1 := by
  have h0 (q : Pattern) (selected : d10237 q = 0) : d69210 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10237, d69210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6732 q selected
    | true =>
      simp only [d10237, d69210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d10238 q = 0) : d69211 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10238, d69211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10238, d69211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1735 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
    | true =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d1736 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d154214 q = 0) : d155887 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d154214, d155887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154214, d155887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154215 q = 0) : d155888 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d154215, d155888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154215, d155888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro13978 (p : Pattern) (selected : d154221 p = 0) : d155894 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154216 q = 0) : d155889 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154216, d155889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13977 q selected
    | true =>
      simp only [d154216, d155889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154217 q = 0) : d155890 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154217, d155890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154217, d155890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154218 q = 0) : d155891 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154218, d155891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154218, d155891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154219 q = 0) : d155892 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154219, d155892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154219, d155892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154220 q = 0) : d155893 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154220, d155893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154220, d155893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154221 q = 0) : d155894 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154221, d155894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154221, d155894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13979 (p : Pattern) (selected : d154227 p = 0) : d155900 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154204 q = 0) : d155877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154204, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13975 q selected
    | true =>
      simp only [d154204, d155877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154205 q = 0) : d155878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154205, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154205, d155878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154206 q = 0) : d155879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154206, d155879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154206, d155879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154207 q = 0) : d155880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154207, d155880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154207, d155880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154226 q = 0) : d155899 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154226, d155899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154226, d155899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154227 q = 0) : d155900 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154227, d155900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154227, d155900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13980 (p : Pattern) (selected : d154233 p = 0) : d155906 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154211 q = 0) : d155884 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154211, d155884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13974 q selected
    | true =>
      simp only [d154211, d155884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13976 q selected
  have h2 (q : Pattern) (selected : d154212 q = 0) : d155885 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154212, d155885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154212, d155885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154213 q = 0) : d155886 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154213, d155886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154213, d155886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154222 q = 0) : d155895 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154222, d155895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13976 q selected
    | true =>
      simp only [d154222, d155895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13978 q selected
  have h5 (q : Pattern) (selected : d154223 q = 0) : d155896 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154223, d155896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154223, d155896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154224 q = 0) : d155897 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154224, d155897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154224, d155897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154225 q = 0) : d155898 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154225, d155898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154225, d155898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154228 q = 0) : d155901 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154228, d155901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13976 q selected
    | true =>
      simp only [d154228, d155901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13979 q selected
  have h9 (q : Pattern) (selected : d154229 q = 0) : d155902 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154229, d155902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154229, d155902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154230 q = 0) : d155903 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154230, d155903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154230, d155903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154231 q = 0) : d155904 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154231, d155904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154231, d155904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154232 q = 0) : d155905 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154232, d155905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154232, d155905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154233 q = 0) : d155906 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154233, d155906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154233, d155906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13981 (p : Pattern) (selected : d154237 p = 0) : d155910 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154228 q = 0) : d155901 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154228, d155901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13976 q selected
    | true =>
      simp only [d154228, d155901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13979 q selected
  have h2 (q : Pattern) (selected : d154229 q = 0) : d155902 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154229, d155902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154229, d155902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154230 q = 0) : d155903 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154230, d155903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154230, d155903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154231 q = 0) : d155904 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154231, d155904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154231, d155904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154236 q = 0) : d155909 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154236, d155909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154236, d155909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154237 q = 0) : d155910 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154237, d155910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154237, d155910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13982 (p : Pattern) (selected : d154243 p = 0) : d155916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154234 q = 0) : d155907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154234, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13980 q selected
    | true =>
      simp only [d154234, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154235 q = 0) : d155908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154235, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154235, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154238 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154238, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13981 q selected
    | true =>
      simp only [d154238, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154239 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154239, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154239, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154240 q = 0) : d155913 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154240, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154240, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154241 q = 0) : d155914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154241, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154241, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154242 q = 0) : d155915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154242, d155915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154242, d155915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154243 q = 0) : d155916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154243, d155916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154243, d155916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13983 (p : Pattern) (selected : d154247 p = 0) : d155920 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154238 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154238, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13981 q selected
    | true =>
      simp only [d154238, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154239 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154239, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154239, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154244 q = 0) : d155917 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154244, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154244, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154245 q = 0) : d155918 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154245, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154245, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154246 q = 0) : d155919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154246, d155919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154246, d155919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154247 q = 0) : d155920 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154247, d155920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154247, d155920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13984 (p : Pattern) (selected : d154253 p = 0) : d156002 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154090 q = 0) : d155907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13951 q selected
    | true =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154091 q = 0) : d155908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154250 q = 0) : d155999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154250, d155999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154250, d155999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154251 q = 0) : d156000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154251, d156000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154251, d156000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154252 q = 0) : d156001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154252, d156001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154252, d156001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154253 q = 0) : d156002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154253, d156002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154253, d156002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13985 (p : Pattern) (selected : d154259 p = 0) : d156008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154127 q = 0) : d155944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154127, d155944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13959 q selected
    | true =>
      simp only [d154127, d155944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13960 q selected
  have h2 (q : Pattern) (selected : d154128 q = 0) : d155945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154128, d155945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154128, d155945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154129 q = 0) : d155946 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154129, d155946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154129, d155946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154130 q = 0) : d155947 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154130, d155947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154130, d155947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154137 q = 0) : d155954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154137, d155954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13961 q selected
    | true =>
      simp only [d154137, d155954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13962 q selected
  have h6 (q : Pattern) (selected : d154138 q = 0) : d155955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154138, d155955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154138, d155955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154139 q = 0) : d155956 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154139, d155956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154139, d155956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154180 q = 0) : d155997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154180, d155997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13969 q selected
    | true =>
      simp only [d154180, d155997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13970 q selected
  have h9 (q : Pattern) (selected : d154248 q = 0) : d155921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154248, d155921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13982 q selected
    | true =>
      simp only [d154248, d155921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13983 q selected
  have h10 (q : Pattern) (selected : d154249 q = 0) : d155998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154249, d155998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154249, d155998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154254 q = 0) : d156003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154254, d156003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13984 q selected
    | true =>
      simp only [d154254, d156003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154255 q = 0) : d156004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154255, d156004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154255, d156004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154256 q = 0) : d156005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154256, d156005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154256, d156005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154257 q = 0) : d156006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154257, d156006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154257, d156006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154258 q = 0) : d156007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154258, d156007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154258, d156007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154259 q = 0) : d156008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154259, d156008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154259, d156008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro13986 (p : Pattern) (selected : d154260 p = 0) : d156009 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154090 q = 0) : d155907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13951 q selected
    | true =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154091 q = 0) : d155908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154096 q = 0) : d155913 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154097 q = 0) : d155914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154097, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154097, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154123 q = 0) : d155940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154123, d155940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154123, d155940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154260 q = 0) : d156009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154260, d156009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154260, d156009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13987 (p : Pattern) (selected : d154261 p = 0) : d156010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154100 q = 0) : d155917 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154101 q = 0) : d155918 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154101, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154101, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154125 q = 0) : d155942 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154125, d155942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154125, d155942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154261 q = 0) : d156010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154261, d156010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154261, d156010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13988 (p : Pattern) (selected : d154266 p = 0) : d156015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154090 q = 0) : d155907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13951 q selected
    | true =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154091 q = 0) : d155908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154096 q = 0) : d155913 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154096, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154131 q = 0) : d155948 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154131, d155948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154131, d155948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154132 q = 0) : d155949 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154132, d155949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154132, d155949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154266 q = 0) : d156015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154266, d156015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154266, d156015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13989 (p : Pattern) (selected : d154267 p = 0) : d156016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154100 q = 0) : d155917 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154100, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154134 q = 0) : d155951 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154134, d155951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154134, d155951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154135 q = 0) : d155952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154135, d155952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154135, d155952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154267 q = 0) : d156016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154267, d156016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154267, d156016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13990 (p : Pattern) (selected : d154271 p = 0) : d156020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154165 q = 0) : d155982 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154165, d155982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13967 q selected
    | true =>
      simp only [d154165, d155982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154166 q = 0) : d155983 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154166, d155983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154166, d155983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154170 q = 0) : d155987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154170, d155987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13968 q selected
    | true =>
      simp only [d154170, d155987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154171 q = 0) : d155988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154171, d155988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154171, d155988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154172 q = 0) : d155989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154172, d155989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154172, d155989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154173 q = 0) : d155990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154173, d155990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154173, d155990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154174 q = 0) : d155991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154174, d155991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154174, d155991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154271 q = 0) : d156020 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154271, d156020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154271, d156020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13991 (p : Pattern) (selected : d154272 p = 0) : d156021 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154170 q = 0) : d155987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154170, d155987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13968 q selected
    | true =>
      simp only [d154170, d155987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154171 q = 0) : d155988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154171, d155988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154171, d155988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154094 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13952 q selected
    | true =>
      simp only [d154094, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154095 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154095, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154176 q = 0) : d155993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154176, d155993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154176, d155993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154177 q = 0) : d155994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154177, d155994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154177, d155994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154178 q = 0) : d155995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154178, d155995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154178, d155995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154272 q = 0) : d156021 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154272, d156021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154272, d156021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13992 (p : Pattern) (selected : d154274 p = 0) : d155929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154234 q = 0) : d155907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154234, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13980 q selected
    | true =>
      simp only [d154234, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154235 q = 0) : d155908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154235, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154235, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154238 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154238, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13981 q selected
    | true =>
      simp only [d154238, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154239 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154239, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154239, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154240 q = 0) : d155913 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154240, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154240, d155913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154241 q = 0) : d155914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154241, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154241, d155914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154242 q = 0) : d155915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154242, d155915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154242, d155915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154274 q = 0) : d155929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154274, d155929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154274, d155929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13993 (p : Pattern) (selected : d154275 p = 0) : d155930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154238 q = 0) : d155911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154238, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13981 q selected
    | true =>
      simp only [d154238, d155911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154239 q = 0) : d155912 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154239, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154239, d155912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154244 q = 0) : d155917 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154244, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154244, d155917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154245 q = 0) : d155918 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154245, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154245, d155918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154246 q = 0) : d155919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154246, d155919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154246, d155919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154275 q = 0) : d155930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154275, d155930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154275, d155930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13994 (p : Pattern) (selected : d154278 p = 0) : d156024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154090 q = 0) : d155907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13951 q selected
    | true =>
      simp only [d154090, d155907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154091 q = 0) : d155908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154091, d155908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154250 q = 0) : d155999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154250, d155999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154250, d155999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154251 q = 0) : d156000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154251, d156000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154251, d156000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154252 q = 0) : d156001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154252, d156001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154252, d156001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154278 q = 0) : d156024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154278, d156024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154278, d156024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13995 (p : Pattern) (selected : d154284 p = 0) : d156030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154127 q = 0) : d155944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154127, d155944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13959 q selected
    | true =>
      simp only [d154127, d155944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13960 q selected
  have h2 (q : Pattern) (selected : d154128 q = 0) : d155945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154128, d155945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154128, d155945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154129 q = 0) : d155946 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154129, d155946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154129, d155946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154130 q = 0) : d155947 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154130, d155947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154130, d155947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154137 q = 0) : d155954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154137, d155954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13961 q selected
    | true =>
      simp only [d154137, d155954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13962 q selected
  have h6 (q : Pattern) (selected : d154138 q = 0) : d155955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154138, d155955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154138, d155955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154139 q = 0) : d155956 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154139, d155956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d154139, d155956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d154180 q = 0) : d155997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154180, d155997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13969 q selected
    | true =>
      simp only [d154180, d155997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13970 q selected
  have h9 (q : Pattern) (selected : d154248 q = 0) : d155921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154248, d155921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13982 q selected
    | true =>
      simp only [d154248, d155921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13983 q selected
  have h10 (q : Pattern) (selected : d154249 q = 0) : d155998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154249, d155998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d154249, d155998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154254 q = 0) : d156003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154254, d156003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13984 q selected
    | true =>
      simp only [d154254, d156003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154255 q = 0) : d156004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154255, d156004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d154255, d156004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d154256 q = 0) : d156005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154256, d156005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154256, d156005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154257 q = 0) : d156006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154257, d156006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154257, d156006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d154258 q = 0) : d156007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154258, d156007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154258, d156007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d154262 q = 0) : d156011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154262, d156011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13986 q selected
    | true =>
      simp only [d154262, d156011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13987 q selected
  have h17 (q : Pattern) (selected : d154263 q = 0) : d156012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154263, d156012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154263, d156012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d154264 q = 0) : d156013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154264, d156013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d154264, d156013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d154265 q = 0) : d156014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154265, d156014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154265, d156014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d154268 q = 0) : d156017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154268, d156017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13988 q selected
    | true =>
      simp only [d154268, d156017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13989 q selected
  have h21 (q : Pattern) (selected : d154269 q = 0) : d156018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154269, d156018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154269, d156018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d154270 q = 0) : d156019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154270, d156019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d154270, d156019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d154273 q = 0) : d156022 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154273, d156022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13990 q selected
    | true =>
      simp only [d154273, d156022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13991 q selected
  have h24 (q : Pattern) (selected : d154276 q = 0) : d155931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154276, d155931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13992 q selected
    | true =>
      simp only [d154276, d155931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13993 q selected
  have h25 (q : Pattern) (selected : d154277 q = 0) : d156023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154277, d156023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d154277, d156023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d154279 q = 0) : d156025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154279, d156025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13994 q selected
    | true =>
      simp only [d154279, d156025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d154280 q = 0) : d156026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154280, d156026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d154280, d156026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d154281 q = 0) : d156027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154281, d156027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d154281, d156027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d154282 q = 0) : d156028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154282, d156028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d154282, d156028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d154283 q = 0) : d156029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154283, d156029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d154283, d156029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d154284 q = 0) : d156030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154284, d156030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154284, d156030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro13996 (p : Pattern) (selected : d154296 p = 0) : d156042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154286 q = 0) : d156032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154286, d156032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13970 q selected
    | true =>
      simp only [d154286, d156032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13954 q selected
  have h2 (q : Pattern) (selected : d154287 q = 0) : d156033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154287, d156033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154287, d156033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154288 q = 0) : d156034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154288, d156034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154288, d156034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154289 q = 0) : d156035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154289, d156035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154289, d156035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154290 q = 0) : d156036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154290, d156036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154290, d156036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154291 q = 0) : d156037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154291, d156037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13954 q selected
    | true =>
      simp only [d154291, d156037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154292 q = 0) : d156038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154292, d156038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154292, d156038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154293 q = 0) : d156039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154293, d156039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154293, d156039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154294 q = 0) : d156040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154294, d156040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154294, d156040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154295 q = 0) : d156041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154295, d156041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154295, d156041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154296 q = 0) : d156042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154296, d156042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154296, d156042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13997 (p : Pattern) (selected : d154302 p = 0) : d156048 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154291 q = 0) : d156037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154291, d156037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13954 q selected
    | true =>
      simp only [d154291, d156037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154292 q = 0) : d156038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154292, d156038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154292, d156038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154293 q = 0) : d156039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154293, d156039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154293, d156039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154294 q = 0) : d156040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154294, d156040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154294, d156040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154295 q = 0) : d156041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154295, d156041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154295, d156041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154297 q = 0) : d156043 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154297, d156043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13957 q selected
    | true =>
      simp only [d154297, d156043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154298 q = 0) : d156044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154298, d156044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154298, d156044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154299 q = 0) : d156045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154299, d156045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d154299, d156045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d154300 q = 0) : d156046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154300, d156046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154300, d156046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154301 q = 0) : d156047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154301, d156047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154301, d156047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d154302 q = 0) : d156048 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154302, d156048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154302, d156048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13998 (p : Pattern) (selected : d154309 p = 0) : d156055 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154273 q = 0) : d156022 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154273, d156022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13990 q selected
    | true =>
      simp only [d154273, d156022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13991 q selected
  have h2 (q : Pattern) (selected : d154276 q = 0) : d155931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154276, d155931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13992 q selected
    | true =>
      simp only [d154276, d155931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13993 q selected
  have h3 (q : Pattern) (selected : d154277 q = 0) : d156023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154277, d156023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154277, d156023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154279 q = 0) : d156025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154279, d156025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13994 q selected
    | true =>
      simp only [d154279, d156025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154280 q = 0) : d156026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154280, d156026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d154280, d156026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d154281 q = 0) : d156027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154281, d156027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154281, d156027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d154307 q = 0) : d156053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154307, d156053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154307, d156053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d154308 q = 0) : d156054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154308, d156054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154308, d156054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d154309 q = 0) : d156055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154309, d156055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154309, d156055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13999 (p : Pattern) (selected : d154311 p = 0) : d156057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154297 q = 0) : d156043 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154297, d156043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13957 q selected
    | true =>
      simp only [d154297, d156043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154298 q = 0) : d156044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154298, d156044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154298, d156044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d154299 q = 0) : d156045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154299, d156045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154299, d156045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d154300 q = 0) : d156046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154300, d156046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154300, d156046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d154301 q = 0) : d156047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154301, d156047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154301, d156047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154311 q = 0) : d156057 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154311, d156057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154311, d156057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
