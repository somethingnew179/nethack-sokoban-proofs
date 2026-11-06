import NetHack.Soko22Hazard87.AndIntroBlocks0182
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro45750 (p : Pattern) (ha : d146836 p = 1) (hb : d150044 p = 1) : d151420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d146836 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20979 q = 1) (hb : d146836 q = 1) : d151368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45739 q ha hb
    | true =>
      simp only [d20979, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20980 q = 1) (hb : d146836 q = 1) : d151369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20981 q = 1) (hb : d146836 q = 1) : d151370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20981, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20982 q = 1) (hb : d146836 q = 1) : d151371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d146836 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20986 q = 1) (hb : d146836 q = 1) : d151375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45740 q ha hb
    | true =>
      simp only [d20986, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20987 q = 1) (hb : d146836 q = 1) : d151376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20988 q = 1) (hb : d146836 q = 1) : d151377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20988, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21009 q = 1) (hb : d146836 q = 1) : d151390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45743 q ha hb
    | true =>
      simp only [d21009, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45726 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150035 q = 1) : d151391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150035, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d21030 q = 1) (hb : d146836 q = 1) : d151396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45744 q ha hb
    | true =>
      simp only [d21030, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21031 q = 1) (hb : d146836 q = 1) : d151397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21031, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150036 q = 1) : d151398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150036, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150037 q = 1) : d151399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150037, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d150038 q = 1) : d151400 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150038, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d146836 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d21037 q = 1) (hb : d146836 q = 1) : d151403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21037, d151403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45746 q ha hb
    | true =>
      simp only [d21037, d151403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21038 q = 1) (hb : d146836 q = 1) : d151404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21038, d151404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21038, d151404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21039 q = 1) (hb : d146836 q = 1) : d151405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21039, d151405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21039, d151405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d21040 q = 1) (hb : d146836 q = 1) : d151406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21040, d151406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21040, d151406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d146836 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d21042 q = 1) (hb : d146836 q = 1) : d151408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21042, d151408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45747 q ha hb
    | true =>
      simp only [d21042, d151408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d21043 q = 1) (hb : d146836 q = 1) : d151409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21043, d151409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21043, d151409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d21044 q = 1) (hb : d146836 q = 1) : d151410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21044, d151410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21044, d151410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21046 q = 1) (hb : d146836 q = 1) : d151412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45748 q ha hb
    | true =>
      simp only [d21046, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45728 q ha hb
  have h27 (q : Pattern) (ha : d146836 q = 1) (hb : d150040 q = 1) : d151413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d150040, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d21051 q = 1) (hb : d146836 q = 1) : d151415 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45749 q ha hb
    | true =>
      simp only [d21051, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d21052 q = 1) (hb : d146836 q = 1) : d151416 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d21052, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d146836 q = 1) (hb : d150041 q = 1) : d151417 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d150041, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d146836 q = 1) (hb : d150042 q = 1) : d151418 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150042, d151418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d150042, d151418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d146836 q = 1) (hb : d150043 q = 1) : d151419 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150043, d151419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150043, d151419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d146836 q = 1) (hb : d150044 q = 1) : d151420 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150044, d151420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150044, d151420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro45751 (p : Pattern) (ha : d146836 p = 1) (hb : d150051 p = 1) : d151429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21046 q = 1) (hb : d146836 q = 1) : d151412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45748 q ha hb
    | true =>
      simp only [d21046, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45728 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150040 q = 1) : d151413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150040, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21051 q = 1) (hb : d146836 q = 1) : d151415 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45749 q ha hb
    | true =>
      simp only [d21051, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21052 q = 1) (hb : d146836 q = 1) : d151416 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21052, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150041 q = 1) : d151417 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150041, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150049 q = 1) : d151427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150049, d151427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150049, d151427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150050 q = 1) : d151428 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150050, d151428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150050, d151428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150051 q = 1) : d151429 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150051, d151429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150051, d151429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45752 (p : Pattern) (ha : d21077 p = 1) (hb : d146836 p = 1) : d148700 p = 1 := by
  have h0 (q : Pattern) (ha : d21075 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21076 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21077 q = 1) (hb : d146836 q = 1) : d148700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21077, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21077, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45753 (p : Pattern) (ha : d21083 p = 1) (hb : d146836 p = 1) : d151440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d146836 q = 1) : d151435 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45752 q ha hb
    | true =>
      simp only [d21078, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d146836 q = 1) : d151436 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d146836 q = 1) : d151437 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d146836 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20933 q = 1) (hb : d146836 q = 1) : d151322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
    | true =>
      simp only [d20933, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20934 q = 1) (hb : d146836 q = 1) : d151323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20935 q = 1) (hb : d146836 q = 1) : d151324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21081 q = 1) (hb : d146836 q = 1) : d151438 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d146836 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20936 q = 1) (hb : d146836 q = 1) : d151325 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20936, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21082 q = 1) (hb : d146836 q = 1) : d151439 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21082, d151439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21082, d151439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21083 q = 1) (hb : d146836 q = 1) : d151440 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21083, d151440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21083, d151440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro45754 (p : Pattern) (ha : d21089 p = 1) (hb : d146836 p = 1) : d151446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21084 q = 1) (hb : d146836 q = 1) : d151441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21084, d151441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45753 q ha hb
    | true =>
      simp only [d21084, d151441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21085 q = 1) (hb : d146836 q = 1) : d151442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21085, d151442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21085, d151442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20939 q = 1) (hb : d146836 q = 1) : d151328 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45732 q ha hb
    | true =>
      simp only [d20939, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20940 q = 1) (hb : d146836 q = 1) : d151329 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21086 q = 1) (hb : d146836 q = 1) : d151443 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21086, d151443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21086, d151443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21087 q = 1) (hb : d146836 q = 1) : d151444 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21087, d151444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21087, d151444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21088 q = 1) (hb : d146836 q = 1) : d151445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21088, d151445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21088, d151445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21089 q = 1) (hb : d146836 q = 1) : d151446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21089, d151446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21089, d151446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45755 (p : Pattern) (ha : d21110 p = 1) (hb : d146836 p = 1) : d151452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d146836 q = 1) : d151328 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45732 q ha hb
    | true =>
      simp only [d20939, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d146836 q = 1) : d151329 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21107 q = 1) (hb : d146836 q = 1) : d151449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21107, d151449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21107, d151449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21108 q = 1) (hb : d146836 q = 1) : d151450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21108, d151450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21108, d151450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21109 q = 1) (hb : d146836 q = 1) : d151451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21109, d151451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21109, d151451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21110 q = 1) (hb : d146836 q = 1) : d151452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21110, d151452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21110, d151452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45756 (p : Pattern) (ha : d146836 p = 1) (hb : d150061 p = 1) : d151458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21090 q = 1) (hb : d146836 q = 1) : d151447 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21090, d151447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45754 q ha hb
    | true =>
      simp only [d21090, d151447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45733 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150057 q = 1) : d151448 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150057, d151448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150057, d151448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21111 q = 1) (hb : d146836 q = 1) : d151453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21111, d151453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45755 q ha hb
    | true =>
      simp only [d21111, d151453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21112 q = 1) (hb : d146836 q = 1) : d151454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21112, d151454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21112, d151454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150058 q = 1) : d151455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150058, d151455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150058, d151455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150059 q = 1) : d151456 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150059, d151456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150059, d151456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150060 q = 1) : d151457 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150060, d151457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150060, d151457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150061 q = 1) : d151458 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150061, d151458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150061, d151458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45757 (p : Pattern) (ha : d146836 p = 1) (hb : d150067 p = 1) : d151464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20967 q = 1) (hb : d146836 q = 1) : d151356 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20967, d151356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20967, d151356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45736 q ha hb
  have h2 (q : Pattern) (ha : d20968 q = 1) (hb : d146836 q = 1) : d151357 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20968, d151357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20968, d151357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20974 q = 1) (hb : d146836 q = 1) : d151363 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45736 q ha hb
    | true =>
      simp only [d20974, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45737 q ha hb
  have h4 (q : Pattern) (ha : d20975 q = 1) (hb : d146836 q = 1) : d151364 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20975, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20976 q = 1) (hb : d146836 q = 1) : d151365 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20976, d151365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20976, d151365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150045 q = 1) : d151421 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150045, d151421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45745 q ha hb
    | true =>
      simp only [d150045, d151421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45750 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d146836 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21059 q = 1) (hb : d146836 q = 1) : d151423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21059, d151423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45738 q ha hb
    | true =>
      simp only [d21059, d151423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150046 q = 1) : d151424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150046, d151424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150046, d151424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150047 q = 1) : d151425 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150047, d151425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150047, d151425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150048 q = 1) : d151426 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150048, d151426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150048, d151426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150052 q = 1) : d151430 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150052, d151430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150052, d151430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45751 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d146836 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150053 q = 1) : d151431 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150053, d151431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150053, d151431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150054 q = 1) : d151432 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150054, d151432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150054, d151432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d150055 q = 1) : d151433 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150055, d151433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150055, d151433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d146836 q = 1) (hb : d150056 q = 1) : d151434 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150056, d151434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150056, d151434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146836 q = 1) (hb : d150062 q = 1) : d151459 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150062, d151459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150062, d151459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45756 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d146836 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d146836 q = 1) (hb : d150063 q = 1) : d151460 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150063, d151460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150063, d151460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d146836 q = 1) (hb : d150064 q = 1) : d151461 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150064, d151461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150064, d151461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146836 q = 1) (hb : d150065 q = 1) : d151462 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150065, d151462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150065, d151462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146836 q = 1) (hb : d150066 q = 1) : d151463 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150066, d151463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150066, d151463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d146836 q = 1) (hb : d150067 q = 1) : d151464 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150067, d151464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150067, d151464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro45758 (p : Pattern) (ha : d146836 p = 1) (hb : d150073 p = 1) : d151470 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d146836 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150030 q = 1) : d151346 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150030, d151346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150030, d151346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45735 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150031 q = 1) : d151347 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150031, d151347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150031, d151347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150032 q = 1) : d151348 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150032, d151348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150032, d151348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150033 q = 1) : d151349 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150033, d151349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150033, d151349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150034 q = 1) : d151350 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150034, d151350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150034, d151350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150068 q = 1) : d151465 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150068, d151465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150068, d151465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45757 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150069 q = 1) : d151466 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150069, d151466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150069, d151466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150070 q = 1) : d151467 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150070, d151467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150070, d151467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150071 q = 1) : d151468 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150071, d151468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150071, d151468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150072 q = 1) : d151469 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150072, d151469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150072, d151469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150073 q = 1) : d151470 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150073, d151470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150073, d151470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45759 (p : Pattern) (ha : d21131 p = 1) (hb : d146836 p = 1) : d151473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d146836 q = 1) : d151378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45741 q ha hb
    | true =>
      simp only [d20997, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d146836 q = 1) : d151379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d146836 q = 1) : d151380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d146836 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20894 q = 1) (hb : d146836 q = 1) : d151285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
    | true =>
      simp only [d20894, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20895 q = 1) (hb : d146836 q = 1) : d151286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20896 q = 1) (hb : d146836 q = 1) : d151287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21000 q = 1) (hb : d146836 q = 1) : d151381 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21129 q = 1) (hb : d146836 q = 1) : d151471 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21129, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21130 q = 1) (hb : d146836 q = 1) : d151472 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21130, d151472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21130, d151472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21131 q = 1) (hb : d146836 q = 1) : d151473 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21131, d151473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21131, d151473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro45760 (p : Pattern) (ha : d21135 p = 1) (hb : d146836 p = 1) : d151477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d146836 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20894 q = 1) (hb : d146836 q = 1) : d151285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
    | true =>
      simp only [d20894, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20895 q = 1) (hb : d146836 q = 1) : d151286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20896 q = 1) (hb : d146836 q = 1) : d151287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21129 q = 1) (hb : d146836 q = 1) : d151471 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21129, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21134 q = 1) (hb : d146836 q = 1) : d151476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21134, d151476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21134, d151476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21135 q = 1) (hb : d146836 q = 1) : d151477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21135, d151477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21135, d151477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro45761 (p : Pattern) (ha : d21141 p = 1) (hb : d146836 p = 1) : d151483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45759 q ha hb
    | true =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d146836 q = 1) : d151481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d146836 q = 1) : d151482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21141 q = 1) (hb : d146836 q = 1) : d151483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21141, d151483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21141, d151483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45762 (p : Pattern) (ha : d21145 p = 1) (hb : d146836 p = 1) : d151487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d146836 q = 1) : d151485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d146836 q = 1) : d151486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21145 q = 1) (hb : d146836 q = 1) : d151487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21145, d151487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21145, d151487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45763 (p : Pattern) (ha : d21151 p = 1) (hb : d146836 p = 1) : d151493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d146836 q = 1) : d151488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45761 q ha hb
    | true =>
      simp only [d21146, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45762 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d146836 q = 1) : d151489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d146836 q = 1) : d151490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d146836 q = 1) : d151491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d146836 q = 1) : d151492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21151 q = 1) (hb : d146836 q = 1) : d151493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21151, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21151, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45764 (p : Pattern) (ha : d21154 p = 1) (hb : d146836 p = 1) : d151496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45759 q ha hb
    | true =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d146836 q = 1) : d151481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d146836 q = 1) : d151482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21154 q = 1) (hb : d146836 q = 1) : d151496 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21154, d151496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21154, d151496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45765 (p : Pattern) (ha : d21155 p = 1) (hb : d146836 p = 1) : d151497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d146836 q = 1) : d151485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d146836 q = 1) : d151486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21155 q = 1) (hb : d146836 q = 1) : d151497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21155, d151497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21155, d151497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45766 (p : Pattern) (ha : d21161 p = 1) (hb : d146836 p = 1) : d151503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d146836 q = 1) : d151488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45761 q ha hb
    | true =>
      simp only [d21146, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45762 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d146836 q = 1) : d151489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d146836 q = 1) : d151490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d146836 q = 1) : d151491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d146836 q = 1) : d151492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21156 q = 1) (hb : d146836 q = 1) : d151498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45764 q ha hb
    | true =>
      simp only [d21156, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45765 q ha hb
  have h7 (q : Pattern) (ha : d21157 q = 1) (hb : d146836 q = 1) : d151499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21158 q = 1) (hb : d146836 q = 1) : d151500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21158, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21159 q = 1) (hb : d146836 q = 1) : d151501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21160 q = 1) (hb : d146836 q = 1) : d151502 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21161 q = 1) (hb : d146836 q = 1) : d151503 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21161, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21161, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45767 (p : Pattern) (ha : d21288 p = 1) (hb : d146836 p = 1) : d151579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d146836 q = 1) : d151488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45761 q ha hb
    | true =>
      simp only [d21146, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45762 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d146836 q = 1) : d151489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d146836 q = 1) : d151490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d146836 q = 1) : d151491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d146836 q = 1) : d151492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21283 q = 1) (hb : d146836 q = 1) : d151574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45762 q ha hb
    | true =>
      simp only [d21283, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21284 q = 1) (hb : d146836 q = 1) : d151575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21285 q = 1) (hb : d146836 q = 1) : d151576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21285, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21286 q = 1) (hb : d146836 q = 1) : d151577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21287 q = 1) (hb : d146836 q = 1) : d151578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21288 q = 1) (hb : d146836 q = 1) : d151579 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21288, d151579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21288, d151579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45768 (p : Pattern) (ha : d21294 p = 1) (hb : d146836 p = 1) : d151585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21283 q = 1) (hb : d146836 q = 1) : d151574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45762 q ha hb
    | true =>
      simp only [d21283, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21284 q = 1) (hb : d146836 q = 1) : d151575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21285 q = 1) (hb : d146836 q = 1) : d151576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21285, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21286 q = 1) (hb : d146836 q = 1) : d151577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21287 q = 1) (hb : d146836 q = 1) : d151578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21289 q = 1) (hb : d146836 q = 1) : d151580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45765 q ha hb
    | true =>
      simp only [d21289, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21290 q = 1) (hb : d146836 q = 1) : d151581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21291 q = 1) (hb : d146836 q = 1) : d151582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21291, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21292 q = 1) (hb : d146836 q = 1) : d151583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21293 q = 1) (hb : d146836 q = 1) : d151584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21294 q = 1) (hb : d146836 q = 1) : d151585 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21294, d151585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21294, d151585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45769 (p : Pattern) (ha : d21303 p = 1) (hb : d146836 p = 1) : d151594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21289 q = 1) (hb : d146836 q = 1) : d151580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45765 q ha hb
    | true =>
      simp only [d21289, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21290 q = 1) (hb : d146836 q = 1) : d151581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21291 q = 1) (hb : d146836 q = 1) : d151582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21291, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21292 q = 1) (hb : d146836 q = 1) : d151583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21293 q = 1) (hb : d146836 q = 1) : d151584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21303 q = 1) (hb : d146836 q = 1) : d151594 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21303, d151594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21303, d151594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45770 (p : Pattern) (ha : d21342 p = 1) (hb : d146836 p = 1) : d151622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d146836 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20933 q = 1) (hb : d146836 q = 1) : d151322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
    | true =>
      simp only [d20933, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20934 q = 1) (hb : d146836 q = 1) : d151323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20935 q = 1) (hb : d146836 q = 1) : d151324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21332 q = 1) (hb : d146836 q = 1) : d151612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21332, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21341 q = 1) (hb : d146836 q = 1) : d151621 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21341, d151621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21341, d151621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21342 q = 1) (hb : d146836 q = 1) : d151622 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21342, d151622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21342, d151622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro45771 (p : Pattern) (ha : d21398 p = 1) (hb : d146836 p = 1) : d151645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21343 q = 1) (hb : d146836 q = 1) : d151623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45770 q ha hb
    | true =>
      simp only [d21343, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21344 q = 1) (hb : d146836 q = 1) : d151624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21395 q = 1) (hb : d146836 q = 1) : d151642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21395, d151642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21395, d151642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21396 q = 1) (hb : d146836 q = 1) : d151643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21396, d151643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21396, d151643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21397 q = 1) (hb : d146836 q = 1) : d151644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21397, d151644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21397, d151644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21398 q = 1) (hb : d146836 q = 1) : d151645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21398, d151645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21398, d151645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45772 (p : Pattern) (ha : d21404 p = 1) (hb : d146836 p = 1) : d151651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21399 q = 1) (hb : d146836 q = 1) : d151646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21399, d151646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45771 q ha hb
    | true =>
      simp only [d21399, d151646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21400 q = 1) (hb : d146836 q = 1) : d151647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21400, d151647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21400, d151647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21401 q = 1) (hb : d146836 q = 1) : d151648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21401, d151648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21401, d151648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21402 q = 1) (hb : d146836 q = 1) : d151649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21402, d151649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21402, d151649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21403 q = 1) (hb : d146836 q = 1) : d151650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21403, d151650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21403, d151650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21404 q = 1) (hb : d146836 q = 1) : d151651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21404, d151651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21404, d151651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45773 (p : Pattern) (ha : d21166 p = 1) (hb : d146836 p = 1) : d151508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45759 q ha hb
    | true =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d146836 q = 1) : d151481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d146836 q = 1) : d151507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21166 q = 1) (hb : d146836 q = 1) : d151508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21166, d151508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21166, d151508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45774 (p : Pattern) (ha : d21168 p = 1) (hb : d146836 p = 1) : d151510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d146836 q = 1) : d151485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d146836 q = 1) : d151509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21168 q = 1) (hb : d146836 q = 1) : d151510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21168, d151510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21168, d151510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45775 (p : Pattern) (ha : d21175 p = 1) (hb : d146836 p = 1) : d151517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45759 q ha hb
    | true =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d146836 q = 1) : d151515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d146836 q = 1) : d151516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21175 q = 1) (hb : d146836 q = 1) : d151517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21175, d151517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21175, d151517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45776 (p : Pattern) (ha : d21178 p = 1) (hb : d146836 p = 1) : d151520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d146836 q = 1) : d151518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d146836 q = 1) : d151519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21178 q = 1) (hb : d146836 q = 1) : d151520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21178, d151520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21178, d151520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45777 (p : Pattern) (ha : d21194 p = 1) (hb : d146836 p = 1) : d148790 p = 1 := by
  have h0 (q : Pattern) (ha : d21187 q = 1) (hb : d116750 q = 1) : d21187 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21194 q = 1) (hb : d146836 q = 1) : d148790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21194, d146836, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21194, d146836, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45778 (p : Pattern) (ha : d21198 p = 1) (hb : d146836 p = 1) : d151527 p = 1 := by
  have h0 (q : Pattern) (ha : d20995 q = 1) (hb : d116750 q = 1) : d20995 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21198 q = 1) (hb : d146836 q = 1) : d151527 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21198, d146836, d151527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21198, d146836, d151527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45779 (p : Pattern) (ha : d21204 p = 1) (hb : d146836 p = 1) : d151533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21195 q = 1) (hb : d146836 q = 1) : d151524 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21195, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45777 q ha hb
    | true =>
      simp only [d21195, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45741 q ha hb
  have h2 (q : Pattern) (ha : d21196 q = 1) (hb : d146836 q = 1) : d151525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21196, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21196, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21197 q = 1) (hb : d146836 q = 1) : d151526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21197, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21197, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21199 q = 1) (hb : d146836 q = 1) : d151528 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21199, d151528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45741 q ha hb
    | true =>
      simp only [d21199, d151528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45778 q ha hb
  have h5 (q : Pattern) (ha : d21200 q = 1) (hb : d146836 q = 1) : d151529 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21200, d151529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21200, d151529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21201 q = 1) (hb : d146836 q = 1) : d151530 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21201, d151530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21201, d151530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21202 q = 1) (hb : d146836 q = 1) : d151531 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21202, d151531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21202, d151531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20997 q = 1) (hb : d146836 q = 1) : d151378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45741 q ha hb
    | true =>
      simp only [d20997, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
  have h9 (q : Pattern) (ha : d20998 q = 1) (hb : d146836 q = 1) : d151379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20999 q = 1) (hb : d146836 q = 1) : d151380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d146836 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20894 q = 1) (hb : d146836 q = 1) : d151285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
    | true =>
      simp only [d20894, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20895 q = 1) (hb : d146836 q = 1) : d151286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20896 q = 1) (hb : d146836 q = 1) : d151287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21000 q = 1) (hb : d146836 q = 1) : d151381 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21000, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21203 q = 1) (hb : d146836 q = 1) : d151532 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21203, d151532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21203, d151532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21204 q = 1) (hb : d146836 q = 1) : d151533 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21204, d151533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21204, d151533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro45780 (p : Pattern) (ha : d21210 p = 1) (hb : d146836 p = 1) : d151539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d146836 q = 1) : d151534 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45779 q ha hb
    | true =>
      simp only [d21205, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d146836 q = 1) : d151535 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45759 q ha hb
    | true =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d146836 q = 1) : d151536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d146836 q = 1) : d151537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d146836 q = 1) : d151538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21210 q = 1) (hb : d146836 q = 1) : d151539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21210, d151539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21210, d151539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45781 (p : Pattern) (ha : d21251 p = 1) (hb : d146836 p = 1) : d151545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45759 q ha hb
    | true =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d146836 q = 1) : d151542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d146836 q = 1) : d151543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d146836 q = 1) : d151544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21251 q = 1) (hb : d146836 q = 1) : d151545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21251, d151545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21251, d151545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45782 (p : Pattern) (ha : d146836 p = 1) (hb : d150078 p = 1) : d151551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d146836 q = 1) : d151511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45773 q ha hb
    | true =>
      simp only [d21169, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45774 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d146836 q = 1) : d151512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d146836 q = 1) : d151513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d146836 q = 1) : d151514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d146836 q = 1) : d151521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45775 q ha hb
    | true =>
      simp only [d21179, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45776 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d146836 q = 1) : d151522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d146836 q = 1) : d151523 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d146836 q = 1) : d151540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45780 q ha hb
    | true =>
      simp only [d21211, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45761 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150074 q = 1) : d151541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150074, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d146836 q = 1) : d151546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45781 q ha hb
    | true =>
      simp only [d21252, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d146836 q = 1) : d151547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150075 q = 1) : d151548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150076 q = 1) : d151549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150076, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150077 q = 1) : d151550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150077, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150078 q = 1) : d151551 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150078, d151551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150078, d151551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45783 (p : Pattern) (ha : d21258 p = 1) (hb : d146836 p = 1) : d151552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45759 q ha hb
    | true =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d146836 q = 1) : d151481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d146836 q = 1) : d151507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21258 q = 1) (hb : d146836 q = 1) : d151552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21258, d151552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21258, d151552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45784 (p : Pattern) (ha : d21259 p = 1) (hb : d146836 p = 1) : d151553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d146836 q = 1) : d151485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d146836 q = 1) : d151509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21259 q = 1) (hb : d146836 q = 1) : d151553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21259, d151553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21259, d151553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45785 (p : Pattern) (ha : d21264 p = 1) (hb : d146836 p = 1) : d151558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45759 q ha hb
    | true =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d146836 q = 1) : d151515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d146836 q = 1) : d151516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21264 q = 1) (hb : d146836 q = 1) : d151558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21264, d151558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21264, d151558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45786 (p : Pattern) (ha : d21265 p = 1) (hb : d146836 p = 1) : d151559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45760 q ha hb
    | true =>
      simp only [d21136, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d146836 q = 1) : d151518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d146836 q = 1) : d151519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21265 q = 1) (hb : d146836 q = 1) : d151559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21265, d151559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21265, d151559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45787 (p : Pattern) (ha : d21269 p = 1) (hb : d146836 p = 1) : d151563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d146836 q = 1) : d151534 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45779 q ha hb
    | true =>
      simp only [d21205, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d146836 q = 1) : d151535 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45759 q ha hb
    | true =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d146836 q = 1) : d151536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d146836 q = 1) : d151537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d146836 q = 1) : d151538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21269 q = 1) (hb : d146836 q = 1) : d151563 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21269, d151563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21269, d151563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45788 (p : Pattern) (ha : d21275 p = 1) (hb : d146836 p = 1) : d151566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45759 q ha hb
    | true =>
      simp only [d21132, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d146836 q = 1) : d151542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d146836 q = 1) : d151543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d146836 q = 1) : d151544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21275 q = 1) (hb : d146836 q = 1) : d151566 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21275, d151566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21275, d151566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45789 (p : Pattern) (ha : d146836 p = 1) (hb : d150083 p = 1) : d151572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d146836 q = 1) : d151511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45773 q ha hb
    | true =>
      simp only [d21169, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45774 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d146836 q = 1) : d151512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d146836 q = 1) : d151513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d146836 q = 1) : d151514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d146836 q = 1) : d151521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45775 q ha hb
    | true =>
      simp only [d21179, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45776 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d146836 q = 1) : d151522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d146836 q = 1) : d151523 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d146836 q = 1) : d151540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45780 q ha hb
    | true =>
      simp only [d21211, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45761 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150074 q = 1) : d151541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150074, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d146836 q = 1) : d151546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45781 q ha hb
    | true =>
      simp only [d21252, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d146836 q = 1) : d151547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150075 q = 1) : d151548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150076 q = 1) : d151549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150076, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150077 q = 1) : d151550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150077, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21260 q = 1) (hb : d146836 q = 1) : d151554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21260, d151554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45783 q ha hb
    | true =>
      simp only [d21260, d151554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45784 q ha hb
  have h16 (q : Pattern) (ha : d21261 q = 1) (hb : d146836 q = 1) : d151555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21261, d151555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21261, d151555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21262 q = 1) (hb : d146836 q = 1) : d151556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21262, d151556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21262, d151556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21263 q = 1) (hb : d146836 q = 1) : d151557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21263, d151557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21263, d151557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21266 q = 1) (hb : d146836 q = 1) : d151560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21266, d151560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45785 q ha hb
    | true =>
      simp only [d21266, d151560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45786 q ha hb
  have h20 (q : Pattern) (ha : d21267 q = 1) (hb : d146836 q = 1) : d151561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21267, d151561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21267, d151561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21268 q = 1) (hb : d146836 q = 1) : d151562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21268, d151562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21268, d151562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21270 q = 1) (hb : d146836 q = 1) : d151564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45787 q ha hb
    | true =>
      simp only [d21270, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45764 q ha hb
  have h23 (q : Pattern) (ha : d146836 q = 1) (hb : d150079 q = 1) : d151565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150079, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d21276 q = 1) (hb : d146836 q = 1) : d151567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45788 q ha hb
    | true =>
      simp only [d21276, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21277 q = 1) (hb : d146836 q = 1) : d151568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21277, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d146836 q = 1) (hb : d150080 q = 1) : d151569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150080, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d146836 q = 1) (hb : d150081 q = 1) : d151570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150081, d151570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150081, d151570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d146836 q = 1) (hb : d150082 q = 1) : d151571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150082, d151571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150082, d151571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146836 q = 1) (hb : d150083 q = 1) : d151572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150083, d151572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150083, d151572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro45790 (p : Pattern) (ha : d146836 p = 1) (hb : d150090 p = 1) : d151592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21270 q = 1) (hb : d146836 q = 1) : d151564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45787 q ha hb
    | true =>
      simp only [d21270, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45764 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150079 q = 1) : d151565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150079, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21276 q = 1) (hb : d146836 q = 1) : d151567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45788 q ha hb
    | true =>
      simp only [d21276, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21277 q = 1) (hb : d146836 q = 1) : d151568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21277, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150080 q = 1) : d151569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150080, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150088 q = 1) : d151590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150088, d151590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150088, d151590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150089 q = 1) : d151591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150089, d151591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150089, d151591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150090 q = 1) : d151592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150090, d151592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150090, d151592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45791 (p : Pattern) (ha : d21319 p = 1) (hb : d146836 p = 1) : d148863 p = 1 := by
  have h0 (q : Pattern) (ha : d21313 q = 1) (hb : d116750 q = 1) : d21313 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21319 q = 1) (hb : d146836 q = 1) : d148863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21319, d146836, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21319, d146836, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45792 (p : Pattern) (ha : d21323 p = 1) (hb : d146836 p = 1) : d151603 p = 1 := by
  have h0 (q : Pattern) (ha : d21076 q = 1) (hb : d116750 q = 1) : d21076 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21323 q = 1) (hb : d146836 q = 1) : d151603 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21323, d146836, d151603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21323, d146836, d151603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45793 (p : Pattern) (ha : d21329 p = 1) (hb : d146836 p = 1) : d151609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21320 q = 1) (hb : d146836 q = 1) : d151600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21320, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45791 q ha hb
    | true =>
      simp only [d21320, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45752 q ha hb
  have h2 (q : Pattern) (ha : d21321 q = 1) (hb : d146836 q = 1) : d151601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21321, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21321, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21322 q = 1) (hb : d146836 q = 1) : d151602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21322, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21322, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21324 q = 1) (hb : d146836 q = 1) : d151604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21324, d151604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45752 q ha hb
    | true =>
      simp only [d21324, d151604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45792 q ha hb
  have h5 (q : Pattern) (ha : d21325 q = 1) (hb : d146836 q = 1) : d151605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21325, d151605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21325, d151605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21326 q = 1) (hb : d146836 q = 1) : d151606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21326, d151606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21326, d151606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21327 q = 1) (hb : d146836 q = 1) : d151607 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21327, d151607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21327, d151607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21078 q = 1) (hb : d146836 q = 1) : d151435 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45752 q ha hb
    | true =>
      simp only [d21078, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
  have h9 (q : Pattern) (ha : d21079 q = 1) (hb : d146836 q = 1) : d151436 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21080 q = 1) (hb : d146836 q = 1) : d151437 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d146836 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20933 q = 1) (hb : d146836 q = 1) : d151322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
    | true =>
      simp only [d20933, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20934 q = 1) (hb : d146836 q = 1) : d151323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20935 q = 1) (hb : d146836 q = 1) : d151324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21081 q = 1) (hb : d146836 q = 1) : d151438 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21081, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21328 q = 1) (hb : d146836 q = 1) : d151608 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21328, d151608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21328, d151608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21329 q = 1) (hb : d146836 q = 1) : d151609 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21329, d151609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21329, d151609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro45794 (p : Pattern) (ha : d21334 p = 1) (hb : d146836 p = 1) : d151614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d146836 q = 1) : d151435 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45752 q ha hb
    | true =>
      simp only [d21078, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d146836 q = 1) : d151436 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d146836 q = 1) : d151437 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d146836 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20933 q = 1) (hb : d146836 q = 1) : d151322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
    | true =>
      simp only [d20933, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20934 q = 1) (hb : d146836 q = 1) : d151323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20935 q = 1) (hb : d146836 q = 1) : d151324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21081 q = 1) (hb : d146836 q = 1) : d151438 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21332 q = 1) (hb : d146836 q = 1) : d151612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21332, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21333 q = 1) (hb : d146836 q = 1) : d151613 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21333, d151613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21333, d151613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21334 q = 1) (hb : d146836 q = 1) : d151614 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21334, d151614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21334, d151614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro45795 (p : Pattern) (ha : d21340 p = 1) (hb : d146836 p = 1) : d151620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21330 q = 1) (hb : d146836 q = 1) : d151610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21330, d151610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45793 q ha hb
    | true =>
      simp only [d21330, d151610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21331 q = 1) (hb : d146836 q = 1) : d151611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21331, d151611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21331, d151611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21335 q = 1) (hb : d146836 q = 1) : d151615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45794 q ha hb
    | true =>
      simp only [d21335, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21336 q = 1) (hb : d146836 q = 1) : d151616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21337 q = 1) (hb : d146836 q = 1) : d151617 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21337, d151617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21337, d151617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21338 q = 1) (hb : d146836 q = 1) : d151618 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21338, d151618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21338, d151618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21339 q = 1) (hb : d146836 q = 1) : d151619 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21339, d151619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21339, d151619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21340 q = 1) (hb : d146836 q = 1) : d151620 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21340, d151620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21340, d151620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45796 (p : Pattern) (ha : d21348 p = 1) (hb : d146836 p = 1) : d151628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d146836 q = 1) : d151615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45794 q ha hb
    | true =>
      simp only [d21335, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d146836 q = 1) : d151616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21343 q = 1) (hb : d146836 q = 1) : d151623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45770 q ha hb
    | true =>
      simp only [d21343, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21344 q = 1) (hb : d146836 q = 1) : d151624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21345 q = 1) (hb : d146836 q = 1) : d151625 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21345, d151625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21345, d151625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21346 q = 1) (hb : d146836 q = 1) : d151626 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21346, d151626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21346, d151626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21347 q = 1) (hb : d146836 q = 1) : d151627 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21347, d151627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21347, d151627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21348 q = 1) (hb : d146836 q = 1) : d151628 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21348, d151628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21348, d151628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45797 (p : Pattern) (ha : d21387 p = 1) (hb : d146836 p = 1) : d151634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d146836 q = 1) : d151615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45794 q ha hb
    | true =>
      simp only [d21335, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d146836 q = 1) : d151616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21384 q = 1) (hb : d146836 q = 1) : d151631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21384, d151631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21384, d151631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21385 q = 1) (hb : d146836 q = 1) : d151632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21385, d151632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21385, d151632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21386 q = 1) (hb : d146836 q = 1) : d151633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21386, d151633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21386, d151633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21387 q = 1) (hb : d146836 q = 1) : d151634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21387, d151634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21387, d151634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45798 (p : Pattern) (ha : d146836 p = 1) (hb : d150100 p = 1) : d151640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21349 q = 1) (hb : d146836 q = 1) : d151629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21349, d151629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45795 q ha hb
    | true =>
      simp only [d21349, d151629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45796 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150096 q = 1) : d151630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150096, d151630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150096, d151630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21388 q = 1) (hb : d146836 q = 1) : d151635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21388, d151635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45797 q ha hb
    | true =>
      simp only [d21388, d151635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21389 q = 1) (hb : d146836 q = 1) : d151636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21389, d151636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21389, d151636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150097 q = 1) : d151637 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150097, d151637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150097, d151637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150098 q = 1) : d151638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150098, d151638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150098, d151638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150099 q = 1) : d151639 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150099, d151639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150099, d151639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150100 q = 1) : d151640 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150100, d151640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150100, d151640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45799 (p : Pattern) (ha : d146836 p = 1) (hb : d150106 p = 1) : d151657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21152 q = 1) (hb : d146836 q = 1) : d151494 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21152, d151494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21152, d151494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45763 q ha hb
  have h2 (q : Pattern) (ha : d21153 q = 1) (hb : d146836 q = 1) : d151495 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21153, d151495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21153, d151495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21162 q = 1) (hb : d146836 q = 1) : d151504 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45763 q ha hb
    | true =>
      simp only [d21162, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45766 q ha hb
  have h4 (q : Pattern) (ha : d21163 q = 1) (hb : d146836 q = 1) : d151505 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21163, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21164 q = 1) (hb : d146836 q = 1) : d151506 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21164, d151506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21164, d151506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150084 q = 1) : d151573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150084, d151573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45782 q ha hb
    | true =>
      simp only [d150084, d151573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45789 q ha hb
  have h7 (q : Pattern) (ha : d21295 q = 1) (hb : d146836 q = 1) : d151586 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21295, d151586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45767 q ha hb
    | true =>
      simp only [d21295, d151586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45768 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150085 q = 1) : d151587 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150085, d151587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150085, d151587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150086 q = 1) : d151588 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150086, d151588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150086, d151588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150087 q = 1) : d151589 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150087, d151589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150087, d151589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150091 q = 1) : d151593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150091, d151593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150091, d151593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45790 q ha hb
  have h12 (q : Pattern) (ha : d21304 q = 1) (hb : d146836 q = 1) : d151595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21304, d151595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21304, d151595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45769 q ha hb
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150092 q = 1) : d151596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150092, d151596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150092, d151596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150093 q = 1) : d151597 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150093, d151597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150093, d151597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150094 q = 1) : d151598 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150094, d151598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150094, d151598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d150095 q = 1) : d151599 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150095, d151599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150095, d151599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146836 q = 1) (hb : d150101 q = 1) : d151641 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150101, d151641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150101, d151641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45798 q ha hb
  have h18 (q : Pattern) (ha : d21405 q = 1) (hb : d146836 q = 1) : d151652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21405, d151652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21405, d151652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45772 q ha hb
  have h19 (q : Pattern) (ha : d146836 q = 1) (hb : d150102 q = 1) : d151653 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150102, d151653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150102, d151653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d146836 q = 1) (hb : d150103 q = 1) : d151654 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150103, d151654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150103, d151654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146836 q = 1) (hb : d150104 q = 1) : d151655 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150104, d151655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150104, d151655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146836 q = 1) (hb : d150105 q = 1) : d151656 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150105, d151656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150105, d151656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146836 q = 1) (hb : d150106 q = 1) : d151657 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150106, d151657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150106, d151657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro45800 (p : Pattern) (ha : d146836 p = 1) (hb : d150112 p = 1) : d151663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150107 q = 1) : d151658 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150107, d151658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150107, d151658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45799 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150108 q = 1) : d151659 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150108, d151659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150108, d151659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150109 q = 1) : d151660 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150109, d151660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150109, d151660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150110 q = 1) : d151661 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150110, d151661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150110, d151661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150111 q = 1) : d151662 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150111, d151662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150111, d151662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150112 q = 1) : d151663 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150112, d151663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150112, d151663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45801 (p : Pattern) (ha : d21419 p = 1) (hb : d146836 p = 1) : d148790 p = 1 := by
  have h0 (q : Pattern) (ha : d21187 q = 1) (hb : d116750 q = 1) : d21187 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21419 q = 1) (hb : d146836 q = 1) : d148790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21419, d146836, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21419, d146836, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45802 (p : Pattern) (ha : d21420 p = 1) (hb : d146836 p = 1) : d148642 p = 1 := by
  have h0 (q : Pattern) (ha : d20994 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21420 q = 1) (hb : d146836 q = 1) : d148642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21420, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21420, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45803 (p : Pattern) (ha : d21430 p = 1) (hb : d146836 p = 1) : d151671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21421 q = 1) (hb : d146836 q = 1) : d151524 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45801 q ha hb
    | true =>
      simp only [d21421, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45802 q ha hb
  have h2 (q : Pattern) (ha : d21422 q = 1) (hb : d146836 q = 1) : d151525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21423 q = 1) (hb : d146836 q = 1) : d151526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d762 q = 1) (hb : d146836 q = 1) : d762 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21424 q = 1) (hb : d146836 q = 1) : d151665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45802 q ha hb
    | true =>
      simp only [d21424, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21425 q = 1) (hb : d146836 q = 1) : d151666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21426 q = 1) (hb : d146836 q = 1) : d151667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21427 q = 1) (hb : d146836 q = 1) : d151668 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21427, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21428 q = 1) (hb : d146836 q = 1) : d151669 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21428, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21429 q = 1) (hb : d146836 q = 1) : d151670 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21429, d151670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21429, d151670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21430 q = 1) (hb : d146836 q = 1) : d151671 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21430, d151671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21430, d151671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro45804 (p : Pattern) (ha : d21434 p = 1) (hb : d146836 p = 1) : d151675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d146836 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21424 q = 1) (hb : d146836 q = 1) : d151665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45802 q ha hb
    | true =>
      simp only [d21424, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21425 q = 1) (hb : d146836 q = 1) : d151666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21426 q = 1) (hb : d146836 q = 1) : d151667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21428 q = 1) (hb : d146836 q = 1) : d151669 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21428, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21433 q = 1) (hb : d146836 q = 1) : d151674 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21433, d151674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21433, d151674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21434 q = 1) (hb : d146836 q = 1) : d151675 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21434, d151675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21434, d151675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro45805 (p : Pattern) (ha : d21440 p = 1) (hb : d146836 p = 1) : d151681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45803 q ha hb
    | true =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d146836 q = 1) : d151679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d146836 q = 1) : d151680 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21440 q = 1) (hb : d146836 q = 1) : d151681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21440, d151681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21440, d151681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45806 (p : Pattern) (ha : d21444 p = 1) (hb : d146836 p = 1) : d151685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d146836 q = 1) : d151683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d146836 q = 1) : d151684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21444 q = 1) (hb : d146836 q = 1) : d151685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21444, d151685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21444, d151685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45807 (p : Pattern) (ha : d21450 p = 1) (hb : d146836 p = 1) : d151691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d146836 q = 1) : d151686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45805 q ha hb
    | true =>
      simp only [d21445, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45806 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d146836 q = 1) : d151687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d146836 q = 1) : d151688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d146836 q = 1) : d151689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d146836 q = 1) : d151690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21450 q = 1) (hb : d146836 q = 1) : d151691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21450, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21450, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45808 (p : Pattern) (ha : d21453 p = 1) (hb : d146836 p = 1) : d151694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45803 q ha hb
    | true =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d146836 q = 1) : d151679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d146836 q = 1) : d151680 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21453 q = 1) (hb : d146836 q = 1) : d151694 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21453, d151694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21453, d151694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45809 (p : Pattern) (ha : d21454 p = 1) (hb : d146836 p = 1) : d151695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d146836 q = 1) : d151683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d146836 q = 1) : d151684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21454 q = 1) (hb : d146836 q = 1) : d151695 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21454, d151695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21454, d151695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45810 (p : Pattern) (ha : d21460 p = 1) (hb : d146836 p = 1) : d151701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d146836 q = 1) : d151686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45805 q ha hb
    | true =>
      simp only [d21445, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45806 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d146836 q = 1) : d151687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d146836 q = 1) : d151688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d146836 q = 1) : d151689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d146836 q = 1) : d151690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21455 q = 1) (hb : d146836 q = 1) : d151696 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45808 q ha hb
    | true =>
      simp only [d21455, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45809 q ha hb
  have h7 (q : Pattern) (ha : d21456 q = 1) (hb : d146836 q = 1) : d151697 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21457 q = 1) (hb : d146836 q = 1) : d151698 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21457, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21458 q = 1) (hb : d146836 q = 1) : d151699 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21459 q = 1) (hb : d146836 q = 1) : d151700 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21460 q = 1) (hb : d146836 q = 1) : d151701 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21460, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21460, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45811 (p : Pattern) (ha : d21591 p = 1) (hb : d146836 p = 1) : d151777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d146836 q = 1) : d151686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45805 q ha hb
    | true =>
      simp only [d21445, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45806 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d146836 q = 1) : d151687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d146836 q = 1) : d151688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d146836 q = 1) : d151689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d146836 q = 1) : d151690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21586 q = 1) (hb : d146836 q = 1) : d151772 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45806 q ha hb
    | true =>
      simp only [d21586, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21587 q = 1) (hb : d146836 q = 1) : d151773 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21588 q = 1) (hb : d146836 q = 1) : d151774 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21588, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21589 q = 1) (hb : d146836 q = 1) : d151775 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21590 q = 1) (hb : d146836 q = 1) : d151776 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21591 q = 1) (hb : d146836 q = 1) : d151777 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21591, d151777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21591, d151777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45812 (p : Pattern) (ha : d21597 p = 1) (hb : d146836 p = 1) : d151783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21586 q = 1) (hb : d146836 q = 1) : d151772 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45806 q ha hb
    | true =>
      simp only [d21586, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21587 q = 1) (hb : d146836 q = 1) : d151773 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21588 q = 1) (hb : d146836 q = 1) : d151774 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21588, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21589 q = 1) (hb : d146836 q = 1) : d151775 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21590 q = 1) (hb : d146836 q = 1) : d151776 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21592 q = 1) (hb : d146836 q = 1) : d151778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45809 q ha hb
    | true =>
      simp only [d21592, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21593 q = 1) (hb : d146836 q = 1) : d151779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21594 q = 1) (hb : d146836 q = 1) : d151780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21594, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21595 q = 1) (hb : d146836 q = 1) : d151781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21596 q = 1) (hb : d146836 q = 1) : d151782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21597 q = 1) (hb : d146836 q = 1) : d151783 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21597, d151783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21597, d151783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45813 (p : Pattern) (ha : d21606 p = 1) (hb : d146836 p = 1) : d151792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21592 q = 1) (hb : d146836 q = 1) : d151778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45809 q ha hb
    | true =>
      simp only [d21592, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21593 q = 1) (hb : d146836 q = 1) : d151779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21594 q = 1) (hb : d146836 q = 1) : d151780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21594, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21595 q = 1) (hb : d146836 q = 1) : d151781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21596 q = 1) (hb : d146836 q = 1) : d151782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21606 q = 1) (hb : d146836 q = 1) : d151792 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21606, d151792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21606, d151792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45814 (p : Pattern) (ha : d21633 p = 1) (hb : d146836 p = 1) : d148700 p = 1 := by
  have h0 (q : Pattern) (ha : d21075 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21633 q = 1) (hb : d146836 q = 1) : d148700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21633, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21633, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45815 (p : Pattern) (ha : d21655 p = 1) (hb : d146836 p = 1) : d151824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d146836 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21637 q = 1) (hb : d146836 q = 1) : d151806 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45814 q ha hb
    | true =>
      simp only [d21637, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21638 q = 1) (hb : d146836 q = 1) : d151807 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21639 q = 1) (hb : d146836 q = 1) : d151808 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21645 q = 1) (hb : d146836 q = 1) : d151814 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21645, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21654 q = 1) (hb : d146836 q = 1) : d151823 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21654, d151823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21654, d151823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21655 q = 1) (hb : d146836 q = 1) : d151824 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21655, d151824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21655, d151824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro45816 (p : Pattern) (ha : d21715 p = 1) (hb : d146836 p = 1) : d151847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21656 q = 1) (hb : d146836 q = 1) : d151825 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45815 q ha hb
    | true =>
      simp only [d21656, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21657 q = 1) (hb : d146836 q = 1) : d151826 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21712 q = 1) (hb : d146836 q = 1) : d151844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21712, d151844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21712, d151844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21713 q = 1) (hb : d146836 q = 1) : d151845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21713, d151845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21713, d151845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21714 q = 1) (hb : d146836 q = 1) : d151846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21714, d151846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21714, d151846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21715 q = 1) (hb : d146836 q = 1) : d151847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21715, d151847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21715, d151847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45817 (p : Pattern) (ha : d21721 p = 1) (hb : d146836 p = 1) : d151853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21716 q = 1) (hb : d146836 q = 1) : d151848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21716, d151848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45816 q ha hb
    | true =>
      simp only [d21716, d151848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21717 q = 1) (hb : d146836 q = 1) : d151849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21717, d151849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21717, d151849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21718 q = 1) (hb : d146836 q = 1) : d151850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21718, d151850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21718, d151850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21719 q = 1) (hb : d146836 q = 1) : d151851 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21719, d151851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21719, d151851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21720 q = 1) (hb : d146836 q = 1) : d151852 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21720, d151852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21720, d151852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21721 q = 1) (hb : d146836 q = 1) : d151853 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21721, d151853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21721, d151853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45818 (p : Pattern) (ha : d21465 p = 1) (hb : d146836 p = 1) : d151706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45803 q ha hb
    | true =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d146836 q = 1) : d151679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d146836 q = 1) : d151705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21465 q = 1) (hb : d146836 q = 1) : d151706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21465, d151706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21465, d151706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45819 (p : Pattern) (ha : d21467 p = 1) (hb : d146836 p = 1) : d151708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d146836 q = 1) : d151683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d146836 q = 1) : d151707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21467 q = 1) (hb : d146836 q = 1) : d151708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21467, d151708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21467, d151708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45820 (p : Pattern) (ha : d21474 p = 1) (hb : d146836 p = 1) : d151715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45803 q ha hb
    | true =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d146836 q = 1) : d151713 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d146836 q = 1) : d151714 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21474 q = 1) (hb : d146836 q = 1) : d151715 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21474, d151715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21474, d151715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45821 (p : Pattern) (ha : d21477 p = 1) (hb : d146836 p = 1) : d151718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d146836 q = 1) : d151716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d146836 q = 1) : d151717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21477 q = 1) (hb : d146836 q = 1) : d151718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21477, d151718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21477, d151718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45822 (p : Pattern) (ha : d21493 p = 1) (hb : d146836 p = 1) : d148978 p = 1 := by
  have h0 (q : Pattern) (ha : d21486 q = 1) (hb : d116750 q = 1) : d21486 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21492 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21493 q = 1) (hb : d146836 q = 1) : d148978 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21493, d146836, d148978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21493, d146836, d148978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45823 (p : Pattern) (ha : d21497 p = 1) (hb : d146836 p = 1) : d151725 p = 1 := by
  have h0 (q : Pattern) (ha : d21418 q = 1) (hb : d116750 q = 1) : d21418 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21497 q = 1) (hb : d146836 q = 1) : d151725 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21497, d146836, d151725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21497, d146836, d151725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45824 (p : Pattern) (ha : d21503 p = 1) (hb : d146836 p = 1) : d151731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21494 q = 1) (hb : d146836 q = 1) : d151722 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21494, d151722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45822 q ha hb
    | true =>
      simp only [d21494, d151722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45801 q ha hb
  have h2 (q : Pattern) (ha : d21495 q = 1) (hb : d146836 q = 1) : d151723 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21495, d151723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21495, d151723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21496 q = 1) (hb : d146836 q = 1) : d151724 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21496, d151724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21496, d151724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21498 q = 1) (hb : d146836 q = 1) : d151726 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21498, d151726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45801 q ha hb
    | true =>
      simp only [d21498, d151726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45823 q ha hb
  have h5 (q : Pattern) (ha : d21499 q = 1) (hb : d146836 q = 1) : d151727 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21499, d151727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21499, d151727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21500 q = 1) (hb : d146836 q = 1) : d151728 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21500, d151728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21500, d151728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21501 q = 1) (hb : d146836 q = 1) : d151729 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21501, d151729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21501, d151729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21421 q = 1) (hb : d146836 q = 1) : d151524 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45801 q ha hb
    | true =>
      simp only [d21421, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45802 q ha hb
  have h9 (q : Pattern) (ha : d21422 q = 1) (hb : d146836 q = 1) : d151525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21423 q = 1) (hb : d146836 q = 1) : d151526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d762 q = 1) (hb : d146836 q = 1) : d762 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d21424 q = 1) (hb : d146836 q = 1) : d151665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45802 q ha hb
    | true =>
      simp only [d21424, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21425 q = 1) (hb : d146836 q = 1) : d151666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21426 q = 1) (hb : d146836 q = 1) : d151667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21427 q = 1) (hb : d146836 q = 1) : d151668 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21427, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21502 q = 1) (hb : d146836 q = 1) : d151730 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21502, d151730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21502, d151730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21503 q = 1) (hb : d146836 q = 1) : d151731 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21503, d151731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21503, d151731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro45825 (p : Pattern) (ha : d21509 p = 1) (hb : d146836 p = 1) : d151737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d146836 q = 1) : d151732 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45824 q ha hb
    | true =>
      simp only [d21504, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d146836 q = 1) : d151733 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45803 q ha hb
    | true =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d146836 q = 1) : d151734 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d146836 q = 1) : d151735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d146836 q = 1) : d151736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21509 q = 1) (hb : d146836 q = 1) : d151737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21509, d151737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21509, d151737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45826 (p : Pattern) (ha : d21554 p = 1) (hb : d146836 p = 1) : d151743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45803 q ha hb
    | true =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d146836 q = 1) : d151740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d146836 q = 1) : d151741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d146836 q = 1) : d151742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21554 q = 1) (hb : d146836 q = 1) : d151743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21554, d151743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21554, d151743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45827 (p : Pattern) (ha : d146836 p = 1) (hb : d150118 p = 1) : d151749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d146836 q = 1) : d151709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45818 q ha hb
    | true =>
      simp only [d21468, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45819 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d146836 q = 1) : d151710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d146836 q = 1) : d151711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d146836 q = 1) : d151712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d146836 q = 1) : d151719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45820 q ha hb
    | true =>
      simp only [d21478, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45821 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d146836 q = 1) : d151720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d146836 q = 1) : d151721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d146836 q = 1) : d151738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45825 q ha hb
    | true =>
      simp only [d21510, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45805 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150114 q = 1) : d151739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150114, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d146836 q = 1) : d151744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45826 q ha hb
    | true =>
      simp only [d21555, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d146836 q = 1) : d151745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150115 q = 1) : d151746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150116 q = 1) : d151747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150116, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150117 q = 1) : d151748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150117, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150118 q = 1) : d151749 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150118, d151749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150118, d151749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45828 (p : Pattern) (ha : d21561 p = 1) (hb : d146836 p = 1) : d151750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45803 q ha hb
    | true =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d146836 q = 1) : d151679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d146836 q = 1) : d151705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21561 q = 1) (hb : d146836 q = 1) : d151750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21561, d151750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21561, d151750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45829 (p : Pattern) (ha : d21562 p = 1) (hb : d146836 p = 1) : d151751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d146836 q = 1) : d151683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d146836 q = 1) : d151707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21562 q = 1) (hb : d146836 q = 1) : d151751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21562, d151751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21562, d151751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45830 (p : Pattern) (ha : d21567 p = 1) (hb : d146836 p = 1) : d151756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45803 q ha hb
    | true =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d146836 q = 1) : d151713 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d146836 q = 1) : d151714 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21567 q = 1) (hb : d146836 q = 1) : d151756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21567, d151756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21567, d151756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45831 (p : Pattern) (ha : d21568 p = 1) (hb : d146836 p = 1) : d151757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45804 q ha hb
    | true =>
      simp only [d21435, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d146836 q = 1) : d151716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d146836 q = 1) : d151717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21568 q = 1) (hb : d146836 q = 1) : d151757 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21568, d151757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21568, d151757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45832 (p : Pattern) (ha : d21572 p = 1) (hb : d146836 p = 1) : d151761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d146836 q = 1) : d151732 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45824 q ha hb
    | true =>
      simp only [d21504, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d146836 q = 1) : d151733 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45803 q ha hb
    | true =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d146836 q = 1) : d151734 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d146836 q = 1) : d151735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d146836 q = 1) : d151736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21572 q = 1) (hb : d146836 q = 1) : d151761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21572, d151761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21572, d151761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45833 (p : Pattern) (ha : d21578 p = 1) (hb : d146836 p = 1) : d151764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45803 q ha hb
    | true =>
      simp only [d21431, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d146836 q = 1) : d151740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d146836 q = 1) : d151741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d146836 q = 1) : d151742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21578 q = 1) (hb : d146836 q = 1) : d151764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21578, d151764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21578, d151764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45834 (p : Pattern) (ha : d146836 p = 1) (hb : d150123 p = 1) : d151770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d146836 q = 1) : d151709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45818 q ha hb
    | true =>
      simp only [d21468, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45819 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d146836 q = 1) : d151710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d146836 q = 1) : d151711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d146836 q = 1) : d151712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d146836 q = 1) : d151719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45820 q ha hb
    | true =>
      simp only [d21478, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45821 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d146836 q = 1) : d151720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d146836 q = 1) : d151721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d146836 q = 1) : d151738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45825 q ha hb
    | true =>
      simp only [d21510, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45805 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150114 q = 1) : d151739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150114, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d146836 q = 1) : d151744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45826 q ha hb
    | true =>
      simp only [d21555, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d146836 q = 1) : d151745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150115 q = 1) : d151746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150116 q = 1) : d151747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150116, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150117 q = 1) : d151748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150117, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21563 q = 1) (hb : d146836 q = 1) : d151752 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21563, d151752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45828 q ha hb
    | true =>
      simp only [d21563, d151752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45829 q ha hb
  have h16 (q : Pattern) (ha : d21564 q = 1) (hb : d146836 q = 1) : d151753 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21564, d151753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21564, d151753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21565 q = 1) (hb : d146836 q = 1) : d151754 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21565, d151754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21565, d151754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21566 q = 1) (hb : d146836 q = 1) : d151755 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21566, d151755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21566, d151755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21569 q = 1) (hb : d146836 q = 1) : d151758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21569, d151758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45830 q ha hb
    | true =>
      simp only [d21569, d151758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45831 q ha hb
  have h20 (q : Pattern) (ha : d21570 q = 1) (hb : d146836 q = 1) : d151759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21570, d151759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21570, d151759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21571 q = 1) (hb : d146836 q = 1) : d151760 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21571, d151760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21571, d151760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21573 q = 1) (hb : d146836 q = 1) : d151762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45832 q ha hb
    | true =>
      simp only [d21573, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45808 q ha hb
  have h23 (q : Pattern) (ha : d146836 q = 1) (hb : d150119 q = 1) : d151763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150119, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d21579 q = 1) (hb : d146836 q = 1) : d151765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45833 q ha hb
    | true =>
      simp only [d21579, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21580 q = 1) (hb : d146836 q = 1) : d151766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21580, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d146836 q = 1) (hb : d150120 q = 1) : d151767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150120, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d146836 q = 1) (hb : d150121 q = 1) : d151768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150121, d151768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150121, d151768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d146836 q = 1) (hb : d150122 q = 1) : d151769 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150122, d151769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150122, d151769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146836 q = 1) (hb : d150123 q = 1) : d151770 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150123, d151770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150123, d151770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro45835 (p : Pattern) (ha : d146836 p = 1) (hb : d150130 p = 1) : d151790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21573 q = 1) (hb : d146836 q = 1) : d151762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45832 q ha hb
    | true =>
      simp only [d21573, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45808 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150119 q = 1) : d151763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150119, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21579 q = 1) (hb : d146836 q = 1) : d151765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45833 q ha hb
    | true =>
      simp only [d21579, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21580 q = 1) (hb : d146836 q = 1) : d151766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21580, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150120 q = 1) : d151767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150120, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150128 q = 1) : d151788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150128, d151788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150128, d151788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150129 q = 1) : d151789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150129, d151789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150129, d151789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150130 q = 1) : d151790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150130, d151790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150130, d151790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45836 (p : Pattern) (ha : d21622 p = 1) (hb : d146836 p = 1) : d149051 p = 1 := by
  have h0 (q : Pattern) (ha : d21616 q = 1) (hb : d116750 q = 1) : d21616 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21622 q = 1) (hb : d146836 q = 1) : d149051 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21622, d146836, d149051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21622, d146836, d149051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45837 (p : Pattern) (ha : d21624 p = 1) (hb : d146836 p = 1) : d148863 p = 1 := by
  have h0 (q : Pattern) (ha : d21313 q = 1) (hb : d116750 q = 1) : d21313 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21623 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21624 q = 1) (hb : d146836 q = 1) : d148863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21624, d146836, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21624, d146836, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45838 (p : Pattern) (ha : d21628 p = 1) (hb : d146836 p = 1) : d151801 p = 1 := by
  have h0 (q : Pattern) (ha : d21623 q = 1) (hb : d116750 q = 1) : d21623 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21628 q = 1) (hb : d146836 q = 1) : d151801 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21628, d146836, d151801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21628, d146836, d151801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45839 (p : Pattern) (ha : d21642 p = 1) (hb : d146836 p = 1) : d151811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21625 q = 1) (hb : d146836 q = 1) : d151798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21625, d151798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45836 q ha hb
    | true =>
      simp only [d21625, d151798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45837 q ha hb
  have h2 (q : Pattern) (ha : d21626 q = 1) (hb : d146836 q = 1) : d151799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21626, d151799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21626, d151799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21627 q = 1) (hb : d146836 q = 1) : d151800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21627, d151800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21627, d151800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21629 q = 1) (hb : d146836 q = 1) : d151802 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21629, d151802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45837 q ha hb
    | true =>
      simp only [d21629, d151802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45838 q ha hb
  have h5 (q : Pattern) (ha : d21630 q = 1) (hb : d146836 q = 1) : d151803 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21630, d151803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21630, d151803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21631 q = 1) (hb : d146836 q = 1) : d151804 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21631, d151804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21631, d151804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21632 q = 1) (hb : d146836 q = 1) : d151805 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21632, d151805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21632, d151805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21634 q = 1) (hb : d146836 q = 1) : d151600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45837 q ha hb
    | true =>
      simp only [d21634, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45814 q ha hb
  have h9 (q : Pattern) (ha : d21635 q = 1) (hb : d146836 q = 1) : d151601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21636 q = 1) (hb : d146836 q = 1) : d151602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d986 q = 1) (hb : d146836 q = 1) : d986 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d21637 q = 1) (hb : d146836 q = 1) : d151806 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45814 q ha hb
    | true =>
      simp only [d21637, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21638 q = 1) (hb : d146836 q = 1) : d151807 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21639 q = 1) (hb : d146836 q = 1) : d151808 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21640 q = 1) (hb : d146836 q = 1) : d151809 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21640, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21641 q = 1) (hb : d146836 q = 1) : d151810 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21641, d151810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21641, d151810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21642 q = 1) (hb : d146836 q = 1) : d151811 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21642, d151811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21642, d151811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro45840 (p : Pattern) (ha : d21647 p = 1) (hb : d146836 p = 1) : d151816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21634 q = 1) (hb : d146836 q = 1) : d151600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45837 q ha hb
    | true =>
      simp only [d21634, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45814 q ha hb
  have h2 (q : Pattern) (ha : d21635 q = 1) (hb : d146836 q = 1) : d151601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21636 q = 1) (hb : d146836 q = 1) : d151602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d986 q = 1) (hb : d146836 q = 1) : d986 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21637 q = 1) (hb : d146836 q = 1) : d151806 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45814 q ha hb
    | true =>
      simp only [d21637, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21638 q = 1) (hb : d146836 q = 1) : d151807 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21639 q = 1) (hb : d146836 q = 1) : d151808 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21640 q = 1) (hb : d146836 q = 1) : d151809 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21640, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21645 q = 1) (hb : d146836 q = 1) : d151814 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21645, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21646 q = 1) (hb : d146836 q = 1) : d151815 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21646, d151815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21646, d151815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21647 q = 1) (hb : d146836 q = 1) : d151816 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21647, d151816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21647, d151816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro45841 (p : Pattern) (ha : d21653 p = 1) (hb : d146836 p = 1) : d151822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21643 q = 1) (hb : d146836 q = 1) : d151812 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21643, d151812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45839 q ha hb
    | true =>
      simp only [d21643, d151812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21644 q = 1) (hb : d146836 q = 1) : d151813 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21644, d151813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21644, d151813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21648 q = 1) (hb : d146836 q = 1) : d151817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45840 q ha hb
    | true =>
      simp only [d21648, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21649 q = 1) (hb : d146836 q = 1) : d151818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21650 q = 1) (hb : d146836 q = 1) : d151819 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21650, d151819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21650, d151819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21651 q = 1) (hb : d146836 q = 1) : d151820 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21651, d151820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21651, d151820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21652 q = 1) (hb : d146836 q = 1) : d151821 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21652, d151821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21652, d151821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21653 q = 1) (hb : d146836 q = 1) : d151822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21653, d151822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21653, d151822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45842 (p : Pattern) (ha : d21661 p = 1) (hb : d146836 p = 1) : d151830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d146836 q = 1) : d151817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45840 q ha hb
    | true =>
      simp only [d21648, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d146836 q = 1) : d151818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21656 q = 1) (hb : d146836 q = 1) : d151825 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45815 q ha hb
    | true =>
      simp only [d21656, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21657 q = 1) (hb : d146836 q = 1) : d151826 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21658 q = 1) (hb : d146836 q = 1) : d151827 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21658, d151827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21658, d151827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21659 q = 1) (hb : d146836 q = 1) : d151828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21659, d151828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21659, d151828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21660 q = 1) (hb : d146836 q = 1) : d151829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21660, d151829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21660, d151829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21661 q = 1) (hb : d146836 q = 1) : d151830 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21661, d151830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21661, d151830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45843 (p : Pattern) (ha : d21704 p = 1) (hb : d146836 p = 1) : d151836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d146836 q = 1) : d151817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45840 q ha hb
    | true =>
      simp only [d21648, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d146836 q = 1) : d151818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21701 q = 1) (hb : d146836 q = 1) : d151833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21701, d151833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21701, d151833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21702 q = 1) (hb : d146836 q = 1) : d151834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21702, d151834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21702, d151834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21703 q = 1) (hb : d146836 q = 1) : d151835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21703, d151835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21703, d151835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21704 q = 1) (hb : d146836 q = 1) : d151836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21704, d151836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21704, d151836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45844 (p : Pattern) (ha : d146836 p = 1) (hb : d150140 p = 1) : d151842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21662 q = 1) (hb : d146836 q = 1) : d151831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21662, d151831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45841 q ha hb
    | true =>
      simp only [d21662, d151831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45842 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150136 q = 1) : d151832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150136, d151832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150136, d151832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21705 q = 1) (hb : d146836 q = 1) : d151837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21705, d151837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45843 q ha hb
    | true =>
      simp only [d21705, d151837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21706 q = 1) (hb : d146836 q = 1) : d151838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21706, d151838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21706, d151838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150137 q = 1) : d151839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150137, d151839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150137, d151839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150138 q = 1) : d151840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150138, d151840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150138, d151840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150139 q = 1) : d151841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150139, d151841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150139, d151841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150140 q = 1) : d151842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150140, d151842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150140, d151842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45845 (p : Pattern) (ha : d146836 p = 1) (hb : d150146 p = 1) : d151859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21451 q = 1) (hb : d146836 q = 1) : d151692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21451, d151692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21451, d151692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45807 q ha hb
  have h2 (q : Pattern) (ha : d21452 q = 1) (hb : d146836 q = 1) : d151693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21452, d151693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21452, d151693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21461 q = 1) (hb : d146836 q = 1) : d151702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45807 q ha hb
    | true =>
      simp only [d21461, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45810 q ha hb
  have h4 (q : Pattern) (ha : d21462 q = 1) (hb : d146836 q = 1) : d151703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21462, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21463 q = 1) (hb : d146836 q = 1) : d151704 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21463, d151704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21463, d151704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150124 q = 1) : d151771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150124, d151771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45827 q ha hb
    | true =>
      simp only [d150124, d151771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45834 q ha hb
  have h7 (q : Pattern) (ha : d21598 q = 1) (hb : d146836 q = 1) : d151784 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21598, d151784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45811 q ha hb
    | true =>
      simp only [d21598, d151784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45812 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150125 q = 1) : d151785 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150125, d151785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150125, d151785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150126 q = 1) : d151786 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150126, d151786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150126, d151786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150127 q = 1) : d151787 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150127, d151787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150127, d151787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150131 q = 1) : d151791 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150131, d151791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150131, d151791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45835 q ha hb
  have h12 (q : Pattern) (ha : d21607 q = 1) (hb : d146836 q = 1) : d151793 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21607, d151793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21607, d151793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45813 q ha hb
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150132 q = 1) : d151794 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150132, d151794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150132, d151794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150133 q = 1) : d151795 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150133, d151795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150133, d151795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150134 q = 1) : d151796 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150134, d151796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150134, d151796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d150135 q = 1) : d151797 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150135, d151797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150135, d151797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146836 q = 1) (hb : d150141 q = 1) : d151843 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150141, d151843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150141, d151843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45844 q ha hb
  have h18 (q : Pattern) (ha : d21722 q = 1) (hb : d146836 q = 1) : d151854 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21722, d151854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21722, d151854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45817 q ha hb
  have h19 (q : Pattern) (ha : d146836 q = 1) (hb : d150142 q = 1) : d151855 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150142, d151855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150142, d151855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d146836 q = 1) (hb : d150143 q = 1) : d151856 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150143, d151856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150143, d151856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146836 q = 1) (hb : d150144 q = 1) : d151857 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150144, d151857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150144, d151857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146836 q = 1) (hb : d150145 q = 1) : d151858 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150145, d151858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150145, d151858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146836 q = 1) (hb : d150146 q = 1) : d151859 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150146, d151859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150146, d151859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro45846 (p : Pattern) (ha : d146836 p = 1) (hb : d150152 p = 1) : d151865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150147 q = 1) : d151860 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150147, d151860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150147, d151860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45845 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150148 q = 1) : d151861 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150148, d151861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150148, d151861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150149 q = 1) : d151862 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150149, d151862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150149, d151862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150150 q = 1) : d151863 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150150, d151863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150150, d151863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150151 q = 1) : d151864 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150151, d151864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150151, d151864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150152 q = 1) : d151865 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150152, d151865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150152, d151865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45847 (p : Pattern) (ha : d21753 p = 1) (hb : d146836 p = 1) : d149114 p = 1 := by
  have h0 (q : Pattern) (ha : d21746 q = 1) (hb : d116750 q = 1) : d21746 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21752 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21753 q = 1) (hb : d146836 q = 1) : d149114 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21753, d146836, d149114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21753, d146836, d149114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45848 (p : Pattern) (ha : d21761 p = 1) (hb : d146836 p = 1) : d149118 p = 1 := by
  have h0 (q : Pattern) (ha : d21759 q = 1) (hb : d116750 q = 1) : d21759 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21760 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21761 q = 1) (hb : d146836 q = 1) : d149118 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21761, d146836, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21761, d146836, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45849 (p : Pattern) (ha : d21771 p = 1) (hb : d146836 p = 1) : d151871 p = 1 := by
  have h0 (q : Pattern) (ha : d21770 q = 1) (hb : d116750 q = 1) : d21770 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14772 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21771 q = 1) (hb : d146836 q = 1) : d151871 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21771, d146836, d151871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21771, d146836, d151871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45850 (p : Pattern) (ha : d21777 p = 1) (hb : d146836 p = 1) : d21948 p = 1 := by
  have h0 (q : Pattern) (ha : d21776 q = 1) (hb : d116750 q = 1) : d21776 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14772 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21777 q = 1) (hb : d146836 q = 1) : d21948 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21777, d146836, d21948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21777, d146836, d21948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45851 (p : Pattern) (ha : d21783 p = 1) (hb : d146836 p = 1) : d151881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d146836 q = 1) : d151868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
    | true =>
      simp only [d21762, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d146836 q = 1) : d151869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d146836 q = 1) : d151870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21772 q = 1) (hb : d146836 q = 1) : d151872 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21772, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45849 q ha hb
  have h5 (q : Pattern) (ha : d21773 q = 1) (hb : d146836 q = 1) : d151873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21774 q = 1) (hb : d146836 q = 1) : d151874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21775 q = 1) (hb : d146836 q = 1) : d151875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21778 q = 1) (hb : d146836 q = 1) : d151876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21778, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45850 q ha hb
  have h9 (q : Pattern) (ha : d21779 q = 1) (hb : d146836 q = 1) : d151877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21780 q = 1) (hb : d146836 q = 1) : d151878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21781 q = 1) (hb : d146836 q = 1) : d151879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21781, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21782 q = 1) (hb : d146836 q = 1) : d151880 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21782, d151880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21782, d151880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21783 q = 1) (hb : d146836 q = 1) : d151881 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21783, d151881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21783, d151881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro45852 (p : Pattern) (ha : d21787 p = 1) (hb : d146836 p = 1) : d151885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21778 q = 1) (hb : d146836 q = 1) : d151876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21778, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45850 q ha hb
  have h2 (q : Pattern) (ha : d21779 q = 1) (hb : d146836 q = 1) : d151877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21780 q = 1) (hb : d146836 q = 1) : d151878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21781 q = 1) (hb : d146836 q = 1) : d151879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21781, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21786 q = 1) (hb : d146836 q = 1) : d151884 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21786, d151884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21786, d151884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21787 q = 1) (hb : d146836 q = 1) : d151885 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21787, d151885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21787, d151885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45853 (p : Pattern) (ha : d21793 p = 1) (hb : d146836 p = 1) : d151891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45851 q ha hb
    | true =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d146836 q = 1) : d151889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d146836 q = 1) : d151890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21793 q = 1) (hb : d146836 q = 1) : d151891 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21793, d151891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21793, d151891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45854 (p : Pattern) (ha : d21797 p = 1) (hb : d146836 p = 1) : d151895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d146836 q = 1) : d151893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d146836 q = 1) : d151894 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21797 q = 1) (hb : d146836 q = 1) : d151895 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21797, d151895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21797, d151895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45855 (p : Pattern) (ha : d21803 p = 1) (hb : d146836 p = 1) : d151901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d146836 q = 1) : d151896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45853 q ha hb
    | true =>
      simp only [d21798, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45854 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d146836 q = 1) : d151897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d146836 q = 1) : d151898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d146836 q = 1) : d151899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d146836 q = 1) : d151900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21803 q = 1) (hb : d146836 q = 1) : d151901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21803, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21803, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45856 (p : Pattern) (ha : d21806 p = 1) (hb : d146836 p = 1) : d151904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45851 q ha hb
    | true =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d146836 q = 1) : d151889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d146836 q = 1) : d151890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21806 q = 1) (hb : d146836 q = 1) : d151904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21806, d151904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21806, d151904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45857 (p : Pattern) (ha : d21807 p = 1) (hb : d146836 p = 1) : d151905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d146836 q = 1) : d151893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d146836 q = 1) : d151894 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21807 q = 1) (hb : d146836 q = 1) : d151905 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21807, d151905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21807, d151905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45858 (p : Pattern) (ha : d21813 p = 1) (hb : d146836 p = 1) : d151911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d146836 q = 1) : d151896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45853 q ha hb
    | true =>
      simp only [d21798, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45854 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d146836 q = 1) : d151897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d146836 q = 1) : d151898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d146836 q = 1) : d151899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d146836 q = 1) : d151900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21808 q = 1) (hb : d146836 q = 1) : d151906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45856 q ha hb
    | true =>
      simp only [d21808, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45857 q ha hb
  have h7 (q : Pattern) (ha : d21809 q = 1) (hb : d146836 q = 1) : d151907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21810 q = 1) (hb : d146836 q = 1) : d151908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21810, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21811 q = 1) (hb : d146836 q = 1) : d151909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21812 q = 1) (hb : d146836 q = 1) : d151910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21813 q = 1) (hb : d146836 q = 1) : d151911 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21813, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21813, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45859 (p : Pattern) (ha : d21867 p = 1) (hb : d146836 p = 1) : d151946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d146836 q = 1) : d151868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
    | true =>
      simp only [d21762, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d146836 q = 1) : d151869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d146836 q = 1) : d151870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21772 q = 1) (hb : d146836 q = 1) : d151872 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21772, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45849 q ha hb
  have h5 (q : Pattern) (ha : d21773 q = 1) (hb : d146836 q = 1) : d151873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21774 q = 1) (hb : d146836 q = 1) : d151874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21775 q = 1) (hb : d146836 q = 1) : d151875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21865 q = 1) (hb : d146836 q = 1) : d151944 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21865, d151944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21865, d151944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21866 q = 1) (hb : d146836 q = 1) : d151945 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21866, d151945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21866, d151945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21867 q = 1) (hb : d146836 q = 1) : d151946 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21867, d151946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21867, d151946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro45860 (p : Pattern) (ha : d21877 p = 1) (hb : d146836 p = 1) : d151956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21868 q = 1) (hb : d146836 q = 1) : d151947 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45859 q ha hb
    | true =>
      simp only [d21868, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21869 q = 1) (hb : d146836 q = 1) : d151948 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21874 q = 1) (hb : d146836 q = 1) : d151953 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21874, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21874, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21875 q = 1) (hb : d146836 q = 1) : d151954 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21875, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21875, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21876 q = 1) (hb : d146836 q = 1) : d151955 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21876, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21876, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21877 q = 1) (hb : d146836 q = 1) : d151956 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21877, d151956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21877, d151956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45861 (p : Pattern) (ha : d22003 p = 1) (hb : d146836 p = 1) : d152002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21993 q = 1) (hb : d146836 q = 1) : d151992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21993, d151992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45860 q ha hb
    | true =>
      simp only [d21993, d151992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45854 q ha hb
  have h2 (q : Pattern) (ha : d21994 q = 1) (hb : d146836 q = 1) : d151993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21994, d151993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21994, d151993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21995 q = 1) (hb : d146836 q = 1) : d151994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21995, d151994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21995, d151994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21996 q = 1) (hb : d146836 q = 1) : d151995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21996, d151995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21996, d151995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21997 q = 1) (hb : d146836 q = 1) : d151996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21997, d151996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21997, d151996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21998 q = 1) (hb : d146836 q = 1) : d151997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21998, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45854 q ha hb
    | true =>
      simp only [d21998, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21999 q = 1) (hb : d146836 q = 1) : d151998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21999, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21999, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22000 q = 1) (hb : d146836 q = 1) : d151999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22000, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22000, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22001 q = 1) (hb : d146836 q = 1) : d152000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22001, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22001, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22002 q = 1) (hb : d146836 q = 1) : d152001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22002, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22002, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22003 q = 1) (hb : d146836 q = 1) : d152002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22003, d152002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22003, d152002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45862 (p : Pattern) (ha : d22009 p = 1) (hb : d146836 p = 1) : d152008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21998 q = 1) (hb : d146836 q = 1) : d151997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21998, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45854 q ha hb
    | true =>
      simp only [d21998, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21999 q = 1) (hb : d146836 q = 1) : d151998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21999, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21999, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22000 q = 1) (hb : d146836 q = 1) : d151999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22000, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22000, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22001 q = 1) (hb : d146836 q = 1) : d152000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22001, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22001, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22002 q = 1) (hb : d146836 q = 1) : d152001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22002, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22002, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22004 q = 1) (hb : d146836 q = 1) : d152003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22004, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45857 q ha hb
    | true =>
      simp only [d22004, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22005 q = 1) (hb : d146836 q = 1) : d152004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22005, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22005, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22006 q = 1) (hb : d146836 q = 1) : d152005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22006, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22006, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22007 q = 1) (hb : d146836 q = 1) : d152006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22007, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22007, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22008 q = 1) (hb : d146836 q = 1) : d152007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22008, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22008, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22009 q = 1) (hb : d146836 q = 1) : d152008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22009, d152008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22009, d152008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45863 (p : Pattern) (ha : d22018 p = 1) (hb : d146836 p = 1) : d152017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22004 q = 1) (hb : d146836 q = 1) : d152003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22004, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45857 q ha hb
    | true =>
      simp only [d22004, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22005 q = 1) (hb : d146836 q = 1) : d152004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22005, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22005, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22006 q = 1) (hb : d146836 q = 1) : d152005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22006, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22006, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22007 q = 1) (hb : d146836 q = 1) : d152006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22007, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22007, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22008 q = 1) (hb : d146836 q = 1) : d152007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22008, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22008, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22018 q = 1) (hb : d146836 q = 1) : d152017 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22018, d152017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22018, d152017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45864 (p : Pattern) (ha : d22069 p = 1) (hb : d146836 p = 1) : d149258 p = 1 := by
  have h0 (q : Pattern) (ha : d22068 q = 1) (hb : d116750 q = 1) : d22068 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22058 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22069 q = 1) (hb : d146836 q = 1) : d149258 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22069, d146836, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22069, d146836, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45865 (p : Pattern) (ha : d22097 p = 1) (hb : d146836 p = 1) : d22174 p = 1 := by
  have h0 (q : Pattern) (ha : d22096 q = 1) (hb : d116750 q = 1) : d22096 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22097 q = 1) (hb : d146836 q = 1) : d22174 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22097, d146836, d22174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22097, d146836, d22174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45866 (p : Pattern) (ha : d22103 p = 1) (hb : d146836 p = 1) : d152057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22098 q = 1) (hb : d146836 q = 1) : d152052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22098, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45865 q ha hb
  have h2 (q : Pattern) (ha : d22099 q = 1) (hb : d146836 q = 1) : d152053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22100 q = 1) (hb : d146836 q = 1) : d152054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22101 q = 1) (hb : d146836 q = 1) : d152055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22101, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22102 q = 1) (hb : d146836 q = 1) : d152056 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22102, d152056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22102, d152056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22103 q = 1) (hb : d146836 q = 1) : d152057 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22103, d152057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22103, d152057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45867 (p : Pattern) (ha : d22197 p = 1) (hb : d146836 p = 1) : d152084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22104 q = 1) (hb : d146836 q = 1) : d152058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45866 q ha hb
    | true =>
      simp only [d22104, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22105 q = 1) (hb : d146836 q = 1) : d152059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22194 q = 1) (hb : d146836 q = 1) : d152081 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22194, d152081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22194, d152081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22195 q = 1) (hb : d146836 q = 1) : d152082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22195, d152082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22195, d152082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22196 q = 1) (hb : d146836 q = 1) : d152083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22196, d152083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22196, d152083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22197 q = 1) (hb : d146836 q = 1) : d152084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22197, d152084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22197, d152084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45868 (p : Pattern) (ha : d22203 p = 1) (hb : d146836 p = 1) : d152090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22198 q = 1) (hb : d146836 q = 1) : d152085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22198, d152085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45867 q ha hb
    | true =>
      simp only [d22198, d152085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22199 q = 1) (hb : d146836 q = 1) : d152086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22199, d152086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22199, d152086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22200 q = 1) (hb : d146836 q = 1) : d152087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22200, d152087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22200, d152087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22201 q = 1) (hb : d146836 q = 1) : d152088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22201, d152088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22201, d152088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22202 q = 1) (hb : d146836 q = 1) : d152089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22202, d152089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22202, d152089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22203 q = 1) (hb : d146836 q = 1) : d152090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22203, d152090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22203, d152090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45869 (p : Pattern) (ha : d21818 p = 1) (hb : d146836 p = 1) : d151916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45851 q ha hb
    | true =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d146836 q = 1) : d151889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21817 q = 1) (hb : d146836 q = 1) : d151915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21817, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21817, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21818 q = 1) (hb : d146836 q = 1) : d151916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21818, d151916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21818, d151916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45870 (p : Pattern) (ha : d21820 p = 1) (hb : d146836 p = 1) : d151918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d146836 q = 1) : d151893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21819 q = 1) (hb : d146836 q = 1) : d151917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21819, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21819, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21820 q = 1) (hb : d146836 q = 1) : d151918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21820, d151918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21820, d151918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45871 (p : Pattern) (ha : d21827 p = 1) (hb : d146836 p = 1) : d151925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45851 q ha hb
    | true =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21825 q = 1) (hb : d146836 q = 1) : d151923 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21825, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21825, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21826 q = 1) (hb : d146836 q = 1) : d151924 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21826, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21826, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21827 q = 1) (hb : d146836 q = 1) : d151925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21827, d151925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21827, d151925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45872 (p : Pattern) (ha : d21830 p = 1) (hb : d146836 p = 1) : d151928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21828 q = 1) (hb : d146836 q = 1) : d151926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21828, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21828, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21829 q = 1) (hb : d146836 q = 1) : d151927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21829, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21829, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21830 q = 1) (hb : d146836 q = 1) : d151928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21830, d151928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21830, d151928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45873 (p : Pattern) (ha : d21846 p = 1) (hb : d146836 p = 1) : d149176 p = 1 := by
  have h0 (q : Pattern) (ha : d21839 q = 1) (hb : d116750 q = 1) : d21839 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21846 q = 1) (hb : d146836 q = 1) : d149176 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21846, d146836, d149176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21846, d146836, d149176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45874 (p : Pattern) (ha : d21856 p = 1) (hb : d146836 p = 1) : d151935 p = 1 := by
  have h0 (q : Pattern) (ha : d21855 q = 1) (hb : d116750 q = 1) : d21855 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21760 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21856 q = 1) (hb : d146836 q = 1) : d151935 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21856, d146836, d151935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21856, d146836, d151935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45875 (p : Pattern) (ha : d21862 p = 1) (hb : d146836 p = 1) : d151941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21847 q = 1) (hb : d146836 q = 1) : d151932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21847, d151932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45873 q ha hb
    | true =>
      simp only [d21847, d151932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
  have h2 (q : Pattern) (ha : d21848 q = 1) (hb : d146836 q = 1) : d151933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21848, d151933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21848, d151933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21849 q = 1) (hb : d146836 q = 1) : d151934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21849, d151934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21849, d151934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21857 q = 1) (hb : d146836 q = 1) : d151936 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21857, d151936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
    | true =>
      simp only [d21857, d151936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45874 q ha hb
  have h5 (q : Pattern) (ha : d21858 q = 1) (hb : d146836 q = 1) : d151937 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21858, d151937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21858, d151937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21859 q = 1) (hb : d146836 q = 1) : d151938 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21859, d151938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21859, d151938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21860 q = 1) (hb : d146836 q = 1) : d151939 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21860, d151939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21860, d151939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21762 q = 1) (hb : d146836 q = 1) : d151868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
    | true =>
      simp only [d21762, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
  have h9 (q : Pattern) (ha : d21763 q = 1) (hb : d146836 q = 1) : d151869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21764 q = 1) (hb : d146836 q = 1) : d151870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21772 q = 1) (hb : d146836 q = 1) : d151872 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21772, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45849 q ha hb
  have h12 (q : Pattern) (ha : d21773 q = 1) (hb : d146836 q = 1) : d151873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21774 q = 1) (hb : d146836 q = 1) : d151874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21775 q = 1) (hb : d146836 q = 1) : d151875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21775, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21861 q = 1) (hb : d146836 q = 1) : d151940 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21861, d151940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21861, d151940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21862 q = 1) (hb : d146836 q = 1) : d151941 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21862, d151941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21862, d151941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro45876 (p : Pattern) (ha : d21873 p = 1) (hb : d146836 p = 1) : d151952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21863 q = 1) (hb : d146836 q = 1) : d151942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21863, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45875 q ha hb
    | true =>
      simp only [d21863, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21864 q = 1) (hb : d146836 q = 1) : d151943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21864, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21864, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21868 q = 1) (hb : d146836 q = 1) : d151947 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45859 q ha hb
    | true =>
      simp only [d21868, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21869 q = 1) (hb : d146836 q = 1) : d151948 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21870 q = 1) (hb : d146836 q = 1) : d151949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21870, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21870, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21871 q = 1) (hb : d146836 q = 1) : d151950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21871, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21871, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21872 q = 1) (hb : d146836 q = 1) : d151951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21872, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21872, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21873 q = 1) (hb : d146836 q = 1) : d151952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21873, d151952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21873, d151952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45877 (p : Pattern) (ha : d21954 p = 1) (hb : d146836 p = 1) : d151881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d146836 q = 1) : d151868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
    | true =>
      simp only [d21762, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d146836 q = 1) : d151869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d146836 q = 1) : d151870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21772 q = 1) (hb : d146836 q = 1) : d151872 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21772, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45849 q ha hb
  have h5 (q : Pattern) (ha : d21773 q = 1) (hb : d146836 q = 1) : d151873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21774 q = 1) (hb : d146836 q = 1) : d151874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21775 q = 1) (hb : d146836 q = 1) : d151875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21948 q = 1) (hb : d146836 q = 1) : d21948 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d21949 q = 1) (hb : d146836 q = 1) : d151876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21949, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21949, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21950 q = 1) (hb : d146836 q = 1) : d151877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21950, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21950, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21951 q = 1) (hb : d146836 q = 1) : d151878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21951, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21951, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21952 q = 1) (hb : d146836 q = 1) : d151879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21952, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21952, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21953 q = 1) (hb : d146836 q = 1) : d151880 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21953, d151880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21953, d151880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21954 q = 1) (hb : d146836 q = 1) : d151881 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21954, d151881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21954, d151881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro45878 (p : Pattern) (ha : d21960 p = 1) (hb : d146836 p = 1) : d151962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21955 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21955, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45877 q ha hb
    | true =>
      simp only [d21955, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21956 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21956, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21956, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21957 q = 1) (hb : d146836 q = 1) : d151959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21957, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21957, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21958 q = 1) (hb : d146836 q = 1) : d151960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21958, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21958, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21959 q = 1) (hb : d146836 q = 1) : d151961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21959, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21959, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21960 q = 1) (hb : d146836 q = 1) : d151962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21960, d151962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21960, d151962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45879 (p : Pattern) (ha : d146836 p = 1) (hb : d150159 p = 1) : d151968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21821 q = 1) (hb : d146836 q = 1) : d151919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21821, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45869 q ha hb
    | true =>
      simp only [d21821, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45870 q ha hb
  have h2 (q : Pattern) (ha : d21822 q = 1) (hb : d146836 q = 1) : d151920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21822, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21822, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21823 q = 1) (hb : d146836 q = 1) : d151921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21823, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21823, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21824 q = 1) (hb : d146836 q = 1) : d151922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21824, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21824, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21831 q = 1) (hb : d146836 q = 1) : d151929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21831, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45871 q ha hb
    | true =>
      simp only [d21831, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45872 q ha hb
  have h6 (q : Pattern) (ha : d21832 q = 1) (hb : d146836 q = 1) : d151930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21832, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21832, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21833 q = 1) (hb : d146836 q = 1) : d151931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21833, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21833, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21878 q = 1) (hb : d146836 q = 1) : d151957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21878, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45876 q ha hb
    | true =>
      simp only [d21878, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45860 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150155 q = 1) : d151958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150155, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21961 q = 1) (hb : d146836 q = 1) : d151963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21961, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45878 q ha hb
    | true =>
      simp only [d21961, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21962 q = 1) (hb : d146836 q = 1) : d151964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21962, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21962, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150156 q = 1) : d151965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150156, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150157 q = 1) : d151966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150157, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150158 q = 1) : d151967 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150158, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150159 q = 1) : d151968 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150159, d151968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150159, d151968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45880 (p : Pattern) (ha : d21967 p = 1) (hb : d146836 p = 1) : d151969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45851 q ha hb
    | true =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d146836 q = 1) : d151889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21817 q = 1) (hb : d146836 q = 1) : d151915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21817, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21817, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21967 q = 1) (hb : d146836 q = 1) : d151969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21967, d151969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21967, d151969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45881 (p : Pattern) (ha : d21968 p = 1) (hb : d146836 p = 1) : d151970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d146836 q = 1) : d151893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21819 q = 1) (hb : d146836 q = 1) : d151917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21819, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21819, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21968 q = 1) (hb : d146836 q = 1) : d151970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21968, d151970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21968, d151970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45882 (p : Pattern) (ha : d21973 p = 1) (hb : d146836 p = 1) : d151975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45851 q ha hb
    | true =>
      simp only [d21784, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21825 q = 1) (hb : d146836 q = 1) : d151923 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21825, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21825, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21826 q = 1) (hb : d146836 q = 1) : d151924 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21826, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21826, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21973 q = 1) (hb : d146836 q = 1) : d151975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21973, d151975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21973, d151975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45883 (p : Pattern) (ha : d21974 p = 1) (hb : d146836 p = 1) : d151976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21828 q = 1) (hb : d146836 q = 1) : d151926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21828, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21828, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21829 q = 1) (hb : d146836 q = 1) : d151927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21829, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21829, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21974 q = 1) (hb : d146836 q = 1) : d151976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21974, d151976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21974, d151976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45884 (p : Pattern) (ha : d21978 p = 1) (hb : d146836 p = 1) : d151980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21863 q = 1) (hb : d146836 q = 1) : d151942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21863, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45875 q ha hb
    | true =>
      simp only [d21863, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21864 q = 1) (hb : d146836 q = 1) : d151943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21864, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21864, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21868 q = 1) (hb : d146836 q = 1) : d151947 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45859 q ha hb
    | true =>
      simp only [d21868, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21869 q = 1) (hb : d146836 q = 1) : d151948 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21870 q = 1) (hb : d146836 q = 1) : d151949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21870, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21870, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21871 q = 1) (hb : d146836 q = 1) : d151950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21871, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21871, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21872 q = 1) (hb : d146836 q = 1) : d151951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21872, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21872, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21978 q = 1) (hb : d146836 q = 1) : d151980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21978, d151980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21978, d151980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45885 (p : Pattern) (ha : d21979 p = 1) (hb : d146836 p = 1) : d151981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21868 q = 1) (hb : d146836 q = 1) : d151947 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45859 q ha hb
    | true =>
      simp only [d21868, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21869 q = 1) (hb : d146836 q = 1) : d151948 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45852 q ha hb
    | true =>
      simp only [d21788, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21874 q = 1) (hb : d146836 q = 1) : d151953 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21874, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21874, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21875 q = 1) (hb : d146836 q = 1) : d151954 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21875, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21875, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21876 q = 1) (hb : d146836 q = 1) : d151955 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21876, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21876, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21979 q = 1) (hb : d146836 q = 1) : d151981 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21979, d151981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21979, d151981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45886 (p : Pattern) (ha : d21985 p = 1) (hb : d146836 p = 1) : d151984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21955 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21955, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45877 q ha hb
    | true =>
      simp only [d21955, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21956 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21956, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21956, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21957 q = 1) (hb : d146836 q = 1) : d151959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21957, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21957, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21958 q = 1) (hb : d146836 q = 1) : d151960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21958, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21958, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21959 q = 1) (hb : d146836 q = 1) : d151961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21959, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21959, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21985 q = 1) (hb : d146836 q = 1) : d151984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21985, d151984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21985, d151984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45887 (p : Pattern) (ha : d146836 p = 1) (hb : d150164 p = 1) : d151990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21821 q = 1) (hb : d146836 q = 1) : d151919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21821, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45869 q ha hb
    | true =>
      simp only [d21821, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45870 q ha hb
  have h2 (q : Pattern) (ha : d21822 q = 1) (hb : d146836 q = 1) : d151920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21822, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21822, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21823 q = 1) (hb : d146836 q = 1) : d151921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21823, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21823, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21824 q = 1) (hb : d146836 q = 1) : d151922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21824, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21824, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21831 q = 1) (hb : d146836 q = 1) : d151929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21831, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45871 q ha hb
    | true =>
      simp only [d21831, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45872 q ha hb
  have h6 (q : Pattern) (ha : d21832 q = 1) (hb : d146836 q = 1) : d151930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21832, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21832, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21833 q = 1) (hb : d146836 q = 1) : d151931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21833, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21833, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21878 q = 1) (hb : d146836 q = 1) : d151957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21878, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45876 q ha hb
    | true =>
      simp only [d21878, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45860 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150155 q = 1) : d151958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150155, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21961 q = 1) (hb : d146836 q = 1) : d151963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21961, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45878 q ha hb
    | true =>
      simp only [d21961, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21962 q = 1) (hb : d146836 q = 1) : d151964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21962, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21962, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150156 q = 1) : d151965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150156, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150157 q = 1) : d151966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150157, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150158 q = 1) : d151967 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150158, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21969 q = 1) (hb : d146836 q = 1) : d151971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21969, d151971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45880 q ha hb
    | true =>
      simp only [d21969, d151971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45881 q ha hb
  have h16 (q : Pattern) (ha : d21970 q = 1) (hb : d146836 q = 1) : d151972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21970, d151972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21970, d151972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21971 q = 1) (hb : d146836 q = 1) : d151973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21971, d151973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21971, d151973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21972 q = 1) (hb : d146836 q = 1) : d151974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21972, d151974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21972, d151974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21975 q = 1) (hb : d146836 q = 1) : d151977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21975, d151977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45882 q ha hb
    | true =>
      simp only [d21975, d151977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45883 q ha hb
  have h20 (q : Pattern) (ha : d21976 q = 1) (hb : d146836 q = 1) : d151978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21976, d151978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21976, d151978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21977 q = 1) (hb : d146836 q = 1) : d151979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21977, d151979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21977, d151979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21980 q = 1) (hb : d146836 q = 1) : d151982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21980, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45884 q ha hb
    | true =>
      simp only [d21980, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45885 q ha hb
  have h23 (q : Pattern) (ha : d146836 q = 1) (hb : d150160 q = 1) : d151983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150160, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d21986 q = 1) (hb : d146836 q = 1) : d151985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21986, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45886 q ha hb
    | true =>
      simp only [d21986, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21987 q = 1) (hb : d146836 q = 1) : d151986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21987, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21987, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d146836 q = 1) (hb : d150161 q = 1) : d151987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150161, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d146836 q = 1) (hb : d150162 q = 1) : d151988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150162, d151988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150162, d151988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d146836 q = 1) (hb : d150163 q = 1) : d151989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150163, d151989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150163, d151989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146836 q = 1) (hb : d150164 q = 1) : d151990 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150164, d151990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150164, d151990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro45888 (p : Pattern) (ha : d146836 p = 1) (hb : d150171 p = 1) : d152015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21980 q = 1) (hb : d146836 q = 1) : d151982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21980, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45884 q ha hb
    | true =>
      simp only [d21980, d151982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45885 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150160 q = 1) : d151983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150160, d151983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21986 q = 1) (hb : d146836 q = 1) : d151985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21986, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45886 q ha hb
    | true =>
      simp only [d21986, d151985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21987 q = 1) (hb : d146836 q = 1) : d151986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21987, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21987, d151986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150161 q = 1) : d151987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150161, d151987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150169 q = 1) : d152013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150169, d152013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150169, d152013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150170 q = 1) : d152014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150170, d152014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150170, d152014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150171 q = 1) : d152015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150171, d152015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150171, d152015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45889 (p : Pattern) (ha : d22042 p = 1) (hb : d146836 p = 1) : d149249 p = 1 := by
  have h0 (q : Pattern) (ha : d22032 q = 1) (hb : d116750 q = 1) : d22032 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22041 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22042 q = 1) (hb : d146836 q = 1) : d149249 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22042, d146836, d149249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22042, d146836, d149249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45890 (p : Pattern) (ha : d22049 p = 1) (hb : d146836 p = 1) : d149253 p = 1 := by
  have h0 (q : Pattern) (ha : d22047 q = 1) (hb : d116750 q = 1) : d22047 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22049 q = 1) (hb : d146836 q = 1) : d149253 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22049, d146836, d149253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22049, d146836, d149253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45891 (p : Pattern) (ha : d22059 p = 1) (hb : d146836 p = 1) : d152026 p = 1 := by
  have h0 (q : Pattern) (ha : d22057 q = 1) (hb : d116750 q = 1) : d22057 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22058 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22059 q = 1) (hb : d146836 q = 1) : d152026 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22059, d146836, d152026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22059, d146836, d152026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45892 (p : Pattern) (ha : d22078 p = 1) (hb : d146836 p = 1) : d152034 p = 1 := by
  have h0 (q : Pattern) (ha : d22077 q = 1) (hb : d116750 q = 1) : d22077 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22078 q = 1) (hb : d146836 q = 1) : d152034 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22078, d146836, d152034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22078, d146836, d152034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45893 (p : Pattern) (ha : d22084 p = 1) (hb : d146836 p = 1) : d152040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22050 q = 1) (hb : d146836 q = 1) : d152023 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22050, d152023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45889 q ha hb
    | true =>
      simp only [d22050, d152023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45890 q ha hb
  have h2 (q : Pattern) (ha : d22051 q = 1) (hb : d146836 q = 1) : d152024 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22051, d152024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22051, d152024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22052 q = 1) (hb : d146836 q = 1) : d152025 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22052, d152025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22052, d152025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22060 q = 1) (hb : d146836 q = 1) : d152027 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22060, d152027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45890 q ha hb
    | true =>
      simp only [d22060, d152027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45891 q ha hb
  have h5 (q : Pattern) (ha : d22061 q = 1) (hb : d146836 q = 1) : d152028 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22061, d152028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22061, d152028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22062 q = 1) (hb : d146836 q = 1) : d152029 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22062, d152029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22062, d152029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22063 q = 1) (hb : d146836 q = 1) : d152030 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22063, d152030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22063, d152030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22070 q = 1) (hb : d146836 q = 1) : d152031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45890 q ha hb
    | true =>
      simp only [d22070, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
  have h9 (q : Pattern) (ha : d22071 q = 1) (hb : d146836 q = 1) : d152032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22072 q = 1) (hb : d146836 q = 1) : d152033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22079 q = 1) (hb : d146836 q = 1) : d152035 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22079, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45892 q ha hb
  have h12 (q : Pattern) (ha : d22080 q = 1) (hb : d146836 q = 1) : d152036 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22081 q = 1) (hb : d146836 q = 1) : d152037 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22082 q = 1) (hb : d146836 q = 1) : d152038 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22082, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22083 q = 1) (hb : d146836 q = 1) : d152039 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22083, d152039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22083, d152039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22084 q = 1) (hb : d146836 q = 1) : d152040 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22084, d152040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22084, d152040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro45894 (p : Pattern) (ha : d22089 p = 1) (hb : d146836 p = 1) : d152045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d146836 q = 1) : d152031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45890 q ha hb
    | true =>
      simp only [d22070, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d146836 q = 1) : d152032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d146836 q = 1) : d152033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22079 q = 1) (hb : d146836 q = 1) : d152035 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22079, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45892 q ha hb
  have h5 (q : Pattern) (ha : d22080 q = 1) (hb : d146836 q = 1) : d152036 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22081 q = 1) (hb : d146836 q = 1) : d152037 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22082 q = 1) (hb : d146836 q = 1) : d152038 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22087 q = 1) (hb : d146836 q = 1) : d152043 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22087, d152043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22087, d152043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22088 q = 1) (hb : d146836 q = 1) : d152044 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22088, d152044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22088, d152044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22089 q = 1) (hb : d146836 q = 1) : d152045 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22089, d152045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22089, d152045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro45895 (p : Pattern) (ha : d22095 p = 1) (hb : d146836 p = 1) : d152051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22085 q = 1) (hb : d146836 q = 1) : d152041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22085, d152041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45893 q ha hb
    | true =>
      simp only [d22085, d152041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22086 q = 1) (hb : d146836 q = 1) : d152042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22086, d152042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22086, d152042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22090 q = 1) (hb : d146836 q = 1) : d152046 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22090, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45894 q ha hb
    | true =>
      simp only [d22090, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22091 q = 1) (hb : d146836 q = 1) : d152047 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22091, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22091, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22092 q = 1) (hb : d146836 q = 1) : d152048 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22092, d152048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22092, d152048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22093 q = 1) (hb : d146836 q = 1) : d152049 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22093, d152049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22093, d152049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22094 q = 1) (hb : d146836 q = 1) : d152050 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22094, d152050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22094, d152050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22095 q = 1) (hb : d146836 q = 1) : d152051 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22095, d152051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22095, d152051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45896 (p : Pattern) (ha : d22109 p = 1) (hb : d146836 p = 1) : d152063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22090 q = 1) (hb : d146836 q = 1) : d152046 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22090, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45894 q ha hb
    | true =>
      simp only [d22090, d152046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22091 q = 1) (hb : d146836 q = 1) : d152047 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22091, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22091, d152047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d146836 q = 1) : d152058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45866 q ha hb
    | true =>
      simp only [d22104, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d146836 q = 1) : d152059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22106 q = 1) (hb : d146836 q = 1) : d152060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22106, d152060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22106, d152060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22107 q = 1) (hb : d146836 q = 1) : d152061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22107, d152061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22107, d152061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22108 q = 1) (hb : d146836 q = 1) : d152062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22108, d152062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22108, d152062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22109 q = 1) (hb : d146836 q = 1) : d152063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22109, d152063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22109, d152063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45897 (p : Pattern) (ha : d22180 p = 1) (hb : d146836 p = 1) : d152067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d146836 q = 1) : d152031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45890 q ha hb
    | true =>
      simp only [d22070, d152031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d146836 q = 1) : d152032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d152032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d146836 q = 1) : d152033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d152033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22079 q = 1) (hb : d146836 q = 1) : d152035 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22079, d152035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45892 q ha hb
  have h5 (q : Pattern) (ha : d22080 q = 1) (hb : d146836 q = 1) : d152036 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d152036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22081 q = 1) (hb : d146836 q = 1) : d152037 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d152037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22082 q = 1) (hb : d146836 q = 1) : d152038 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d152038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22174 q = 1) (hb : d146836 q = 1) : d22174 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d22175 q = 1) (hb : d146836 q = 1) : d152052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22175, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22175, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22176 q = 1) (hb : d146836 q = 1) : d152053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22176, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22176, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22177 q = 1) (hb : d146836 q = 1) : d152054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22177, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22177, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22178 q = 1) (hb : d146836 q = 1) : d152055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22178, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22178, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22179 q = 1) (hb : d146836 q = 1) : d152066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22179, d152066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22179, d152066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22180 q = 1) (hb : d146836 q = 1) : d152067 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22180, d152067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22180, d152067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro45898 (p : Pattern) (ha : d22186 p = 1) (hb : d146836 p = 1) : d152073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22181 q = 1) (hb : d146836 q = 1) : d152068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22181, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45897 q ha hb
    | true =>
      simp only [d22181, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22182 q = 1) (hb : d146836 q = 1) : d152069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22182, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22182, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22183 q = 1) (hb : d146836 q = 1) : d152070 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22183, d152070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22183, d152070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22184 q = 1) (hb : d146836 q = 1) : d152071 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22184, d152071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22184, d152071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22185 q = 1) (hb : d146836 q = 1) : d152072 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22185, d152072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22185, d152072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22186 q = 1) (hb : d146836 q = 1) : d152073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22186, d152073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22186, d152073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45899 (p : Pattern) (ha : d146836 p = 1) (hb : d150181 p = 1) : d152079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22110 q = 1) (hb : d146836 q = 1) : d152064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22110, d152064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45895 q ha hb
    | true =>
      simp only [d22110, d152064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45896 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150177 q = 1) : d152065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150177, d152065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150177, d152065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22187 q = 1) (hb : d146836 q = 1) : d152074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22187, d152074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45898 q ha hb
    | true =>
      simp only [d22187, d152074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22188 q = 1) (hb : d146836 q = 1) : d152075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22188, d152075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22188, d152075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150178 q = 1) : d152076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150178, d152076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150178, d152076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150179 q = 1) : d152077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150179, d152077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150179, d152077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150180 q = 1) : d152078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150180, d152078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150180, d152078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150181 q = 1) : d152079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150181, d152079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150181, d152079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45900 (p : Pattern) (ha : d146836 p = 1) (hb : d150187 p = 1) : d152096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21804 q = 1) (hb : d146836 q = 1) : d151902 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21804, d151902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21804, d151902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45855 q ha hb
  have h2 (q : Pattern) (ha : d21805 q = 1) (hb : d146836 q = 1) : d151903 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21805, d151903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21805, d151903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21814 q = 1) (hb : d146836 q = 1) : d151912 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45855 q ha hb
    | true =>
      simp only [d21814, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45858 q ha hb
  have h4 (q : Pattern) (ha : d21815 q = 1) (hb : d146836 q = 1) : d151913 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21815, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21816 q = 1) (hb : d146836 q = 1) : d151914 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21816, d151914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21816, d151914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150165 q = 1) : d151991 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150165, d151991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45879 q ha hb
    | true =>
      simp only [d150165, d151991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45887 q ha hb
  have h7 (q : Pattern) (ha : d22010 q = 1) (hb : d146836 q = 1) : d152009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22010, d152009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45861 q ha hb
    | true =>
      simp only [d22010, d152009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45862 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150166 q = 1) : d152010 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150166, d152010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150166, d152010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150167 q = 1) : d152011 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150167, d152011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150167, d152011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150168 q = 1) : d152012 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150168, d152012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150168, d152012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150172 q = 1) : d152016 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150172, d152016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150172, d152016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45888 q ha hb
  have h12 (q : Pattern) (ha : d22019 q = 1) (hb : d146836 q = 1) : d152018 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22019, d152018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22019, d152018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45863 q ha hb
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150173 q = 1) : d152019 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150173, d152019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150173, d152019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150174 q = 1) : d152020 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150174, d152020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150174, d152020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150175 q = 1) : d152021 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150175, d152021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150175, d152021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d150176 q = 1) : d152022 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150176, d152022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150176, d152022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146836 q = 1) (hb : d150182 q = 1) : d152080 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150182, d152080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150182, d152080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45899 q ha hb
  have h18 (q : Pattern) (ha : d22204 q = 1) (hb : d146836 q = 1) : d152091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22204, d152091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22204, d152091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45868 q ha hb
  have h19 (q : Pattern) (ha : d146836 q = 1) (hb : d150183 q = 1) : d152092 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150183, d152092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150183, d152092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d146836 q = 1) (hb : d150184 q = 1) : d152093 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150184, d152093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150184, d152093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146836 q = 1) (hb : d150185 q = 1) : d152094 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150185, d152094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150185, d152094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146836 q = 1) (hb : d150186 q = 1) : d152095 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150186, d152095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150186, d152095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146836 q = 1) (hb : d150187 q = 1) : d152096 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150187, d152096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150187, d152096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro45901 (p : Pattern) (ha : d146836 p = 1) (hb : d150193 p = 1) : d152102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150188 q = 1) : d152097 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150188, d152097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150188, d152097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45900 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150189 q = 1) : d152098 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150189, d152098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150189, d152098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150190 q = 1) : d152099 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150190, d152099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150190, d152099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150191 q = 1) : d152100 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150191, d152100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150191, d152100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150192 q = 1) : d152101 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150192, d152101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150192, d152101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150193 q = 1) : d152102 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150193, d152102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150193, d152102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45902 (p : Pattern) (ha : d22231 p = 1) (hb : d146836 p = 1) : d149322 p = 1 := by
  have h0 (q : Pattern) (ha : d22224 q = 1) (hb : d116750 q = 1) : d22224 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22230 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22231 q = 1) (hb : d146836 q = 1) : d149322 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22231, d146836, d149322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22231, d146836, d149322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45903 (p : Pattern) (ha : d22239 p = 1) (hb : d146836 p = 1) : d149326 p = 1 := by
  have h0 (q : Pattern) (ha : d22237 q = 1) (hb : d116750 q = 1) : d22237 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22238 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22239 q = 1) (hb : d146836 q = 1) : d149326 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22239, d146836, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22239, d146836, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45904 (p : Pattern) (ha : d22249 p = 1) (hb : d146836 p = 1) : d152109 p = 1 := by
  have h0 (q : Pattern) (ha : d22248 q = 1) (hb : d116750 q = 1) : d22248 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22249 q = 1) (hb : d146836 q = 1) : d152109 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22249, d146836, d152109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22249, d146836, d152109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45905 (p : Pattern) (ha : d22255 p = 1) (hb : d146836 p = 1) : d22421 p = 1 := by
  have h0 (q : Pattern) (ha : d22254 q = 1) (hb : d116750 q = 1) : d22254 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22255 q = 1) (hb : d146836 q = 1) : d22421 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22255, d146836, d22421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22255, d146836, d22421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45906 (p : Pattern) (ha : d22261 p = 1) (hb : d146836 p = 1) : d152119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d146836 q = 1) : d152106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
    | true =>
      simp only [d22240, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d146836 q = 1) : d152107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d146836 q = 1) : d152108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22250 q = 1) (hb : d146836 q = 1) : d152110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22250, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45904 q ha hb
  have h5 (q : Pattern) (ha : d22251 q = 1) (hb : d146836 q = 1) : d152111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22252 q = 1) (hb : d146836 q = 1) : d152112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22253 q = 1) (hb : d146836 q = 1) : d152113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22256 q = 1) (hb : d146836 q = 1) : d152114 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22256, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22256, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45905 q ha hb
  have h9 (q : Pattern) (ha : d22257 q = 1) (hb : d146836 q = 1) : d152115 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22257, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22257, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22258 q = 1) (hb : d146836 q = 1) : d152116 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22258, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22258, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22259 q = 1) (hb : d146836 q = 1) : d152117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22259, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22259, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22260 q = 1) (hb : d146836 q = 1) : d152118 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22260, d152118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22260, d152118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22261 q = 1) (hb : d146836 q = 1) : d152119 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22261, d152119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22261, d152119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro45907 (p : Pattern) (ha : d22265 p = 1) (hb : d146836 p = 1) : d152123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22256 q = 1) (hb : d146836 q = 1) : d152114 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22256, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22256, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45905 q ha hb
  have h2 (q : Pattern) (ha : d22257 q = 1) (hb : d146836 q = 1) : d152115 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22257, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22257, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22258 q = 1) (hb : d146836 q = 1) : d152116 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22258, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22258, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22259 q = 1) (hb : d146836 q = 1) : d152117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22259, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22259, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22264 q = 1) (hb : d146836 q = 1) : d152122 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22264, d152122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22264, d152122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22265 q = 1) (hb : d146836 q = 1) : d152123 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22265, d152123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22265, d152123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45908 (p : Pattern) (ha : d22271 p = 1) (hb : d146836 p = 1) : d152129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45906 q ha hb
    | true =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d146836 q = 1) : d152127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22270 q = 1) (hb : d146836 q = 1) : d152128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22270, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22270, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22271 q = 1) (hb : d146836 q = 1) : d152129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22271, d152129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22271, d152129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45909 (p : Pattern) (ha : d22275 p = 1) (hb : d146836 p = 1) : d152133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d146836 q = 1) : d152131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22274 q = 1) (hb : d146836 q = 1) : d152132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22274, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22274, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22275 q = 1) (hb : d146836 q = 1) : d152133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22275, d152133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22275, d152133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45910 (p : Pattern) (ha : d22281 p = 1) (hb : d146836 p = 1) : d152139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22276 q = 1) (hb : d146836 q = 1) : d152134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45908 q ha hb
    | true =>
      simp only [d22276, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45909 q ha hb
  have h2 (q : Pattern) (ha : d22277 q = 1) (hb : d146836 q = 1) : d152135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22277, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22278 q = 1) (hb : d146836 q = 1) : d152136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22278, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22279 q = 1) (hb : d146836 q = 1) : d152137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22279, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22280 q = 1) (hb : d146836 q = 1) : d152138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22281 q = 1) (hb : d146836 q = 1) : d152139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22281, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22281, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45911 (p : Pattern) (ha : d22284 p = 1) (hb : d146836 p = 1) : d152142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45906 q ha hb
    | true =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d146836 q = 1) : d152127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22270 q = 1) (hb : d146836 q = 1) : d152128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22270, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22270, d152128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22284 q = 1) (hb : d146836 q = 1) : d152142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22284, d152142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22284, d152142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45912 (p : Pattern) (ha : d22285 p = 1) (hb : d146836 p = 1) : d152143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d146836 q = 1) : d152131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22274 q = 1) (hb : d146836 q = 1) : d152132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22274, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22274, d152132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22285 q = 1) (hb : d146836 q = 1) : d152143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22285, d152143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22285, d152143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45913 (p : Pattern) (ha : d22291 p = 1) (hb : d146836 p = 1) : d152149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22276 q = 1) (hb : d146836 q = 1) : d152134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45908 q ha hb
    | true =>
      simp only [d22276, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45909 q ha hb
  have h2 (q : Pattern) (ha : d22277 q = 1) (hb : d146836 q = 1) : d152135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22277, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22278 q = 1) (hb : d146836 q = 1) : d152136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22278, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22279 q = 1) (hb : d146836 q = 1) : d152137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22279, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22280 q = 1) (hb : d146836 q = 1) : d152138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22286 q = 1) (hb : d146836 q = 1) : d152144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45911 q ha hb
    | true =>
      simp only [d22286, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45912 q ha hb
  have h7 (q : Pattern) (ha : d22287 q = 1) (hb : d146836 q = 1) : d152145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22288 q = 1) (hb : d146836 q = 1) : d152146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22288, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22289 q = 1) (hb : d146836 q = 1) : d152147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22290 q = 1) (hb : d146836 q = 1) : d152148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22291 q = 1) (hb : d146836 q = 1) : d152149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22291, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22291, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45914 (p : Pattern) (ha : d22340 p = 1) (hb : d146836 p = 1) : d152184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d146836 q = 1) : d152106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
    | true =>
      simp only [d22240, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d146836 q = 1) : d152107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d146836 q = 1) : d152108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22250 q = 1) (hb : d146836 q = 1) : d152110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22250, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45904 q ha hb
  have h5 (q : Pattern) (ha : d22251 q = 1) (hb : d146836 q = 1) : d152111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22252 q = 1) (hb : d146836 q = 1) : d152112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22253 q = 1) (hb : d146836 q = 1) : d152113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22338 q = 1) (hb : d146836 q = 1) : d152182 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22338, d152182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22338, d152182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22339 q = 1) (hb : d146836 q = 1) : d152183 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22339, d152183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22339, d152183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22340 q = 1) (hb : d146836 q = 1) : d152184 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22340, d152184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22340, d152184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro45915 (p : Pattern) (ha : d22350 p = 1) (hb : d146836 p = 1) : d152194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22341 q = 1) (hb : d146836 q = 1) : d152185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45914 q ha hb
    | true =>
      simp only [d22341, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22342 q = 1) (hb : d146836 q = 1) : d152186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22347 q = 1) (hb : d146836 q = 1) : d152191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22347, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22347, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22348 q = 1) (hb : d146836 q = 1) : d152192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22348, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22348, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22349 q = 1) (hb : d146836 q = 1) : d152193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22349, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22349, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22350 q = 1) (hb : d146836 q = 1) : d152194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22350, d152194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22350, d152194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45916 (p : Pattern) (ha : d22476 p = 1) (hb : d146836 p = 1) : d152240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22466 q = 1) (hb : d146836 q = 1) : d152230 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22466, d152230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45915 q ha hb
    | true =>
      simp only [d22466, d152230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45909 q ha hb
  have h2 (q : Pattern) (ha : d22467 q = 1) (hb : d146836 q = 1) : d152231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22467, d152231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22467, d152231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22468 q = 1) (hb : d146836 q = 1) : d152232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22468, d152232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22468, d152232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22469 q = 1) (hb : d146836 q = 1) : d152233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22469, d152233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22469, d152233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22470 q = 1) (hb : d146836 q = 1) : d152234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22470, d152234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22470, d152234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22471 q = 1) (hb : d146836 q = 1) : d152235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22471, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45909 q ha hb
    | true =>
      simp only [d22471, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22472 q = 1) (hb : d146836 q = 1) : d152236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22472, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22472, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22473 q = 1) (hb : d146836 q = 1) : d152237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22473, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22473, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22474 q = 1) (hb : d146836 q = 1) : d152238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22474, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22474, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22475 q = 1) (hb : d146836 q = 1) : d152239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22475, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22475, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22476 q = 1) (hb : d146836 q = 1) : d152240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22476, d152240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22476, d152240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45917 (p : Pattern) (ha : d22482 p = 1) (hb : d146836 p = 1) : d152246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22471 q = 1) (hb : d146836 q = 1) : d152235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22471, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45909 q ha hb
    | true =>
      simp only [d22471, d152235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22472 q = 1) (hb : d146836 q = 1) : d152236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22472, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22472, d152236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22473 q = 1) (hb : d146836 q = 1) : d152237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22473, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22473, d152237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22474 q = 1) (hb : d146836 q = 1) : d152238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22474, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22474, d152238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22475 q = 1) (hb : d146836 q = 1) : d152239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22475, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22475, d152239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22477 q = 1) (hb : d146836 q = 1) : d152241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22477, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45912 q ha hb
    | true =>
      simp only [d22477, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22478 q = 1) (hb : d146836 q = 1) : d152242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22478, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22478, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22479 q = 1) (hb : d146836 q = 1) : d152243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22479, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22479, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22480 q = 1) (hb : d146836 q = 1) : d152244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22480, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22480, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22481 q = 1) (hb : d146836 q = 1) : d152245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22481, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22481, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22482 q = 1) (hb : d146836 q = 1) : d152246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22482, d152246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22482, d152246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45918 (p : Pattern) (ha : d22491 p = 1) (hb : d146836 p = 1) : d152255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22477 q = 1) (hb : d146836 q = 1) : d152241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22477, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45912 q ha hb
    | true =>
      simp only [d22477, d152241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22478 q = 1) (hb : d146836 q = 1) : d152242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22478, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22478, d152242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22479 q = 1) (hb : d146836 q = 1) : d152243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22479, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22479, d152243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22480 q = 1) (hb : d146836 q = 1) : d152244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22480, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22480, d152244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22481 q = 1) (hb : d146836 q = 1) : d152245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22481, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22481, d152245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22491 q = 1) (hb : d146836 q = 1) : d152255 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22491, d152255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22491, d152255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45919 (p : Pattern) (ha : d22534 p = 1) (hb : d146836 p = 1) : d149466 p = 1 := by
  have h0 (q : Pattern) (ha : d22533 q = 1) (hb : d116750 q = 1) : d22533 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22523 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22534 q = 1) (hb : d146836 q = 1) : d149466 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22534, d146836, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22534, d146836, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45920 (p : Pattern) (ha : d22562 p = 1) (hb : d146836 p = 1) : d22639 p = 1 := by
  have h0 (q : Pattern) (ha : d22561 q = 1) (hb : d116750 q = 1) : d22561 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22562 q = 1) (hb : d146836 q = 1) : d22639 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22562, d146836, d22639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22562, d146836, d22639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45921 (p : Pattern) (ha : d22568 p = 1) (hb : d146836 p = 1) : d152295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22563 q = 1) (hb : d146836 q = 1) : d152290 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22563, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45920 q ha hb
  have h2 (q : Pattern) (ha : d22564 q = 1) (hb : d146836 q = 1) : d152291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22565 q = 1) (hb : d146836 q = 1) : d152292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22566 q = 1) (hb : d146836 q = 1) : d152293 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22566, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22567 q = 1) (hb : d146836 q = 1) : d152294 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22567, d152294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22567, d152294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22568 q = 1) (hb : d146836 q = 1) : d152295 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22568, d152295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22568, d152295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45922 (p : Pattern) (ha : d22662 p = 1) (hb : d146836 p = 1) : d152322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22569 q = 1) (hb : d146836 q = 1) : d152296 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45921 q ha hb
    | true =>
      simp only [d22569, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22570 q = 1) (hb : d146836 q = 1) : d152297 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22659 q = 1) (hb : d146836 q = 1) : d152319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22659, d152319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22659, d152319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22660 q = 1) (hb : d146836 q = 1) : d152320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22660, d152320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22660, d152320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22661 q = 1) (hb : d146836 q = 1) : d152321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22661, d152321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22661, d152321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22662 q = 1) (hb : d146836 q = 1) : d152322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22662, d152322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22662, d152322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45923 (p : Pattern) (ha : d22668 p = 1) (hb : d146836 p = 1) : d152328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22663 q = 1) (hb : d146836 q = 1) : d152323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22663, d152323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45922 q ha hb
    | true =>
      simp only [d22663, d152323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22664 q = 1) (hb : d146836 q = 1) : d152324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22664, d152324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22664, d152324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22665 q = 1) (hb : d146836 q = 1) : d152325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22665, d152325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22665, d152325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22666 q = 1) (hb : d146836 q = 1) : d152326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22666, d152326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22666, d152326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22667 q = 1) (hb : d146836 q = 1) : d152327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22667, d152327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22667, d152327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22668 q = 1) (hb : d146836 q = 1) : d152328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22668, d152328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22668, d152328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45924 (p : Pattern) (ha : d22296 p = 1) (hb : d146836 p = 1) : d152154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45906 q ha hb
    | true =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d146836 q = 1) : d152127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22295 q = 1) (hb : d146836 q = 1) : d152153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22295, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22295, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22296 q = 1) (hb : d146836 q = 1) : d152154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22296, d152154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22296, d152154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45925 (p : Pattern) (ha : d22298 p = 1) (hb : d146836 p = 1) : d152156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d146836 q = 1) : d152131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22297 q = 1) (hb : d146836 q = 1) : d152155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22297, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22297, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22298 q = 1) (hb : d146836 q = 1) : d152156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22298, d152156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22298, d152156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45926 (p : Pattern) (ha : d22305 p = 1) (hb : d146836 p = 1) : d152163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45906 q ha hb
    | true =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22303 q = 1) (hb : d146836 q = 1) : d152161 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22303, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22303, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22304 q = 1) (hb : d146836 q = 1) : d152162 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22304, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22304, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22305 q = 1) (hb : d146836 q = 1) : d152163 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22305, d152163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22305, d152163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45927 (p : Pattern) (ha : d22308 p = 1) (hb : d146836 p = 1) : d152166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22306 q = 1) (hb : d146836 q = 1) : d152164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22306, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22306, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22307 q = 1) (hb : d146836 q = 1) : d152165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22307, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22307, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22308 q = 1) (hb : d146836 q = 1) : d152166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22308, d152166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22308, d152166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45928 (p : Pattern) (ha : d22319 p = 1) (hb : d146836 p = 1) : d149384 p = 1 := by
  have h0 (q : Pattern) (ha : d22317 q = 1) (hb : d116750 q = 1) : d22317 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22319 q = 1) (hb : d146836 q = 1) : d149384 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22319, d146836, d149384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22319, d146836, d149384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45929 (p : Pattern) (ha : d22329 p = 1) (hb : d146836 p = 1) : d152173 p = 1 := by
  have h0 (q : Pattern) (ha : d22328 q = 1) (hb : d116750 q = 1) : d22328 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22238 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22329 q = 1) (hb : d146836 q = 1) : d152173 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22329, d146836, d152173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22329, d146836, d152173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45930 (p : Pattern) (ha : d22335 p = 1) (hb : d146836 p = 1) : d152179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22320 q = 1) (hb : d146836 q = 1) : d152170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22320, d152170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45928 q ha hb
    | true =>
      simp only [d22320, d152170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
  have h2 (q : Pattern) (ha : d22321 q = 1) (hb : d146836 q = 1) : d152171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22321, d152171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22321, d152171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22322 q = 1) (hb : d146836 q = 1) : d152172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22322, d152172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22322, d152172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22330 q = 1) (hb : d146836 q = 1) : d152174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22330, d152174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
    | true =>
      simp only [d22330, d152174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45929 q ha hb
  have h5 (q : Pattern) (ha : d22331 q = 1) (hb : d146836 q = 1) : d152175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22331, d152175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22331, d152175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22332 q = 1) (hb : d146836 q = 1) : d152176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22332, d152176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22332, d152176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22333 q = 1) (hb : d146836 q = 1) : d152177 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22333, d152177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22333, d152177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22240 q = 1) (hb : d146836 q = 1) : d152106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
    | true =>
      simp only [d22240, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
  have h9 (q : Pattern) (ha : d22241 q = 1) (hb : d146836 q = 1) : d152107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22242 q = 1) (hb : d146836 q = 1) : d152108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22250 q = 1) (hb : d146836 q = 1) : d152110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22250, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45904 q ha hb
  have h12 (q : Pattern) (ha : d22251 q = 1) (hb : d146836 q = 1) : d152111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22252 q = 1) (hb : d146836 q = 1) : d152112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22253 q = 1) (hb : d146836 q = 1) : d152113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22253, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22334 q = 1) (hb : d146836 q = 1) : d152178 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22334, d152178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22334, d152178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22335 q = 1) (hb : d146836 q = 1) : d152179 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22335, d152179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22335, d152179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro45931 (p : Pattern) (ha : d22346 p = 1) (hb : d146836 p = 1) : d152190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22336 q = 1) (hb : d146836 q = 1) : d152180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22336, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45930 q ha hb
    | true =>
      simp only [d22336, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22337 q = 1) (hb : d146836 q = 1) : d152181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22337, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22337, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22341 q = 1) (hb : d146836 q = 1) : d152185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45914 q ha hb
    | true =>
      simp only [d22341, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22342 q = 1) (hb : d146836 q = 1) : d152186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22343 q = 1) (hb : d146836 q = 1) : d152187 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22343, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22343, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22344 q = 1) (hb : d146836 q = 1) : d152188 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22344, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22344, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22345 q = 1) (hb : d146836 q = 1) : d152189 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22345, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22345, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22346 q = 1) (hb : d146836 q = 1) : d152190 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22346, d152190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22346, d152190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45932 (p : Pattern) (ha : d22427 p = 1) (hb : d146836 p = 1) : d152119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d146836 q = 1) : d152106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
    | true =>
      simp only [d22240, d152106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d146836 q = 1) : d152107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d152107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d146836 q = 1) : d152108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d152108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22250 q = 1) (hb : d146836 q = 1) : d152110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22250, d152110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45904 q ha hb
  have h5 (q : Pattern) (ha : d22251 q = 1) (hb : d146836 q = 1) : d152111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d152111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22252 q = 1) (hb : d146836 q = 1) : d152112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d152112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22253 q = 1) (hb : d146836 q = 1) : d152113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d152113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22421 q = 1) (hb : d146836 q = 1) : d22421 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d22422 q = 1) (hb : d146836 q = 1) : d152114 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22422, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22422, d152114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22423 q = 1) (hb : d146836 q = 1) : d152115 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22423, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22423, d152115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22424 q = 1) (hb : d146836 q = 1) : d152116 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22424, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22424, d152116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22425 q = 1) (hb : d146836 q = 1) : d152117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22425, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22425, d152117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22426 q = 1) (hb : d146836 q = 1) : d152118 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22426, d152118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22426, d152118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22427 q = 1) (hb : d146836 q = 1) : d152119 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22427, d152119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22427, d152119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro45933 (p : Pattern) (ha : d22433 p = 1) (hb : d146836 p = 1) : d152200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22428 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22428, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45932 q ha hb
    | true =>
      simp only [d22428, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22429 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22429, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22429, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22430 q = 1) (hb : d146836 q = 1) : d152197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22430, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22430, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22431 q = 1) (hb : d146836 q = 1) : d152198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22431, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22431, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22432 q = 1) (hb : d146836 q = 1) : d152199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22432, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22432, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22433 q = 1) (hb : d146836 q = 1) : d152200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22433, d152200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22433, d152200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45934 (p : Pattern) (ha : d146836 p = 1) (hb : d150201 p = 1) : d152206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22299 q = 1) (hb : d146836 q = 1) : d152157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22299, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45924 q ha hb
    | true =>
      simp only [d22299, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45925 q ha hb
  have h2 (q : Pattern) (ha : d22300 q = 1) (hb : d146836 q = 1) : d152158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22300, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22300, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22301 q = 1) (hb : d146836 q = 1) : d152159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22301, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22301, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22302 q = 1) (hb : d146836 q = 1) : d152160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22302, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22302, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22309 q = 1) (hb : d146836 q = 1) : d152167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22309, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45926 q ha hb
    | true =>
      simp only [d22309, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45927 q ha hb
  have h6 (q : Pattern) (ha : d22310 q = 1) (hb : d146836 q = 1) : d152168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22310, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22310, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22311 q = 1) (hb : d146836 q = 1) : d152169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22311, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22311, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22351 q = 1) (hb : d146836 q = 1) : d152195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22351, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45931 q ha hb
    | true =>
      simp only [d22351, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45915 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150197 q = 1) : d152196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150197, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22434 q = 1) (hb : d146836 q = 1) : d152201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22434, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45933 q ha hb
    | true =>
      simp only [d22434, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22435 q = 1) (hb : d146836 q = 1) : d152202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22435, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22435, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150198 q = 1) : d152203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150198, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150199 q = 1) : d152204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150199, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150200 q = 1) : d152205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150200, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150201 q = 1) : d152206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150201, d152206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150201, d152206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45935 (p : Pattern) (ha : d22440 p = 1) (hb : d146836 p = 1) : d152207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45906 q ha hb
    | true =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d146836 q = 1) : d152127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d152127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22295 q = 1) (hb : d146836 q = 1) : d152153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22295, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22295, d152153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22440 q = 1) (hb : d146836 q = 1) : d152207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22440, d152207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22440, d152207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45936 (p : Pattern) (ha : d22441 p = 1) (hb : d146836 p = 1) : d152208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d146836 q = 1) : d152131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d152131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22297 q = 1) (hb : d146836 q = 1) : d152155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22297, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22297, d152155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22441 q = 1) (hb : d146836 q = 1) : d152208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22441, d152208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22441, d152208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45937 (p : Pattern) (ha : d22446 p = 1) (hb : d146836 p = 1) : d152213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45906 q ha hb
    | true =>
      simp only [d22262, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146836 q = 1) : d152126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d152126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22303 q = 1) (hb : d146836 q = 1) : d152161 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22303, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22303, d152161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22304 q = 1) (hb : d146836 q = 1) : d152162 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22304, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22304, d152162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22446 q = 1) (hb : d146836 q = 1) : d152213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22446, d152213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22446, d152213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45938 (p : Pattern) (ha : d22447 p = 1) (hb : d146836 p = 1) : d152214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146836 q = 1) : d152130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d152130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22306 q = 1) (hb : d146836 q = 1) : d152164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22306, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22306, d152164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22307 q = 1) (hb : d146836 q = 1) : d152165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22307, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22307, d152165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22447 q = 1) (hb : d146836 q = 1) : d152214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22447, d152214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22447, d152214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45939 (p : Pattern) (ha : d22451 p = 1) (hb : d146836 p = 1) : d152218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22336 q = 1) (hb : d146836 q = 1) : d152180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22336, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45930 q ha hb
    | true =>
      simp only [d22336, d152180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22337 q = 1) (hb : d146836 q = 1) : d152181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22337, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22337, d152181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22341 q = 1) (hb : d146836 q = 1) : d152185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45914 q ha hb
    | true =>
      simp only [d22341, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22342 q = 1) (hb : d146836 q = 1) : d152186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22343 q = 1) (hb : d146836 q = 1) : d152187 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22343, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22343, d152187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22344 q = 1) (hb : d146836 q = 1) : d152188 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22344, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22344, d152188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22345 q = 1) (hb : d146836 q = 1) : d152189 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22345, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22345, d152189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22451 q = 1) (hb : d146836 q = 1) : d152218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22451, d152218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22451, d152218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45940 (p : Pattern) (ha : d22452 p = 1) (hb : d146836 p = 1) : d152219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22341 q = 1) (hb : d146836 q = 1) : d152185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45914 q ha hb
    | true =>
      simp only [d22341, d152185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22342 q = 1) (hb : d146836 q = 1) : d152186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d152186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146836 q = 1) : d152124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45907 q ha hb
    | true =>
      simp only [d22266, d152124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146836 q = 1) : d152125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d152125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22347 q = 1) (hb : d146836 q = 1) : d152191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22347, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22347, d152191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22348 q = 1) (hb : d146836 q = 1) : d152192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22348, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22348, d152192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22349 q = 1) (hb : d146836 q = 1) : d152193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22349, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22349, d152193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22452 q = 1) (hb : d146836 q = 1) : d152219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22452, d152219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22452, d152219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45941 (p : Pattern) (ha : d22458 p = 1) (hb : d146836 p = 1) : d152222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22428 q = 1) (hb : d146836 q = 1) : d152120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22428, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45932 q ha hb
    | true =>
      simp only [d22428, d152120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22429 q = 1) (hb : d146836 q = 1) : d152121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22429, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22429, d152121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22430 q = 1) (hb : d146836 q = 1) : d152197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22430, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22430, d152197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22431 q = 1) (hb : d146836 q = 1) : d152198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22431, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22431, d152198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22432 q = 1) (hb : d146836 q = 1) : d152199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22432, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22432, d152199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22458 q = 1) (hb : d146836 q = 1) : d152222 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22458, d152222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22458, d152222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45942 (p : Pattern) (ha : d146836 p = 1) (hb : d150206 p = 1) : d152228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22299 q = 1) (hb : d146836 q = 1) : d152157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22299, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45924 q ha hb
    | true =>
      simp only [d22299, d152157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45925 q ha hb
  have h2 (q : Pattern) (ha : d22300 q = 1) (hb : d146836 q = 1) : d152158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22300, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22300, d152158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22301 q = 1) (hb : d146836 q = 1) : d152159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22301, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22301, d152159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22302 q = 1) (hb : d146836 q = 1) : d152160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22302, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22302, d152160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22309 q = 1) (hb : d146836 q = 1) : d152167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22309, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45926 q ha hb
    | true =>
      simp only [d22309, d152167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45927 q ha hb
  have h6 (q : Pattern) (ha : d22310 q = 1) (hb : d146836 q = 1) : d152168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22310, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22310, d152168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22311 q = 1) (hb : d146836 q = 1) : d152169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22311, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22311, d152169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22351 q = 1) (hb : d146836 q = 1) : d152195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22351, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45931 q ha hb
    | true =>
      simp only [d22351, d152195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45915 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150197 q = 1) : d152196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150197, d152196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22434 q = 1) (hb : d146836 q = 1) : d152201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22434, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45933 q ha hb
    | true =>
      simp only [d22434, d152201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22435 q = 1) (hb : d146836 q = 1) : d152202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22435, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22435, d152202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150198 q = 1) : d152203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150198, d152203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150199 q = 1) : d152204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150199, d152204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150200 q = 1) : d152205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150200, d152205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22442 q = 1) (hb : d146836 q = 1) : d152209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22442, d152209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45935 q ha hb
    | true =>
      simp only [d22442, d152209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45936 q ha hb
  have h16 (q : Pattern) (ha : d22443 q = 1) (hb : d146836 q = 1) : d152210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22443, d152210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22443, d152210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22444 q = 1) (hb : d146836 q = 1) : d152211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22444, d152211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22444, d152211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22445 q = 1) (hb : d146836 q = 1) : d152212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22445, d152212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22445, d152212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22448 q = 1) (hb : d146836 q = 1) : d152215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22448, d152215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45937 q ha hb
    | true =>
      simp only [d22448, d152215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45938 q ha hb
  have h20 (q : Pattern) (ha : d22449 q = 1) (hb : d146836 q = 1) : d152216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22449, d152216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22449, d152216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d22450 q = 1) (hb : d146836 q = 1) : d152217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22450, d152217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22450, d152217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22453 q = 1) (hb : d146836 q = 1) : d152220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22453, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45939 q ha hb
    | true =>
      simp only [d22453, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45940 q ha hb
  have h23 (q : Pattern) (ha : d146836 q = 1) (hb : d150202 q = 1) : d152221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150202, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d22459 q = 1) (hb : d146836 q = 1) : d152223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22459, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45941 q ha hb
    | true =>
      simp only [d22459, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d22460 q = 1) (hb : d146836 q = 1) : d152224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22460, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22460, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d146836 q = 1) (hb : d150203 q = 1) : d152225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150203, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d146836 q = 1) (hb : d150204 q = 1) : d152226 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150204, d152226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150204, d152226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d146836 q = 1) (hb : d150205 q = 1) : d152227 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150205, d152227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150205, d152227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146836 q = 1) (hb : d150206 q = 1) : d152228 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150206, d152228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150206, d152228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro45943 (p : Pattern) (ha : d146836 p = 1) (hb : d150213 p = 1) : d152253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22453 q = 1) (hb : d146836 q = 1) : d152220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22453, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45939 q ha hb
    | true =>
      simp only [d22453, d152220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45940 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150202 q = 1) : d152221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150202, d152221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22459 q = 1) (hb : d146836 q = 1) : d152223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22459, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45941 q ha hb
    | true =>
      simp only [d22459, d152223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22460 q = 1) (hb : d146836 q = 1) : d152224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22460, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22460, d152224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150203 q = 1) : d152225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150203, d152225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150211 q = 1) : d152251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150211, d152251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150211, d152251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150212 q = 1) : d152252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150212, d152252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150212, d152252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150213 q = 1) : d152253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150213, d152253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150213, d152253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45944 (p : Pattern) (ha : d22507 p = 1) (hb : d146836 p = 1) : d149457 p = 1 := by
  have h0 (q : Pattern) (ha : d22501 q = 1) (hb : d116750 q = 1) : d22501 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22507 q = 1) (hb : d146836 q = 1) : d149457 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22507, d146836, d149457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22507, d146836, d149457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45945 (p : Pattern) (ha : d22514 p = 1) (hb : d146836 p = 1) : d149461 p = 1 := by
  have h0 (q : Pattern) (ha : d22512 q = 1) (hb : d116750 q = 1) : d22512 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22513 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22514 q = 1) (hb : d146836 q = 1) : d149461 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22514, d146836, d149461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22514, d146836, d149461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45946 (p : Pattern) (ha : d22524 p = 1) (hb : d146836 p = 1) : d152264 p = 1 := by
  have h0 (q : Pattern) (ha : d22522 q = 1) (hb : d116750 q = 1) : d22522 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22523 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22524 q = 1) (hb : d146836 q = 1) : d152264 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22524, d146836, d152264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22524, d146836, d152264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45947 (p : Pattern) (ha : d22543 p = 1) (hb : d146836 p = 1) : d152272 p = 1 := by
  have h0 (q : Pattern) (ha : d22542 q = 1) (hb : d116750 q = 1) : d22542 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22543 q = 1) (hb : d146836 q = 1) : d152272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22543, d146836, d152272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22543, d146836, d152272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45948 (p : Pattern) (ha : d22549 p = 1) (hb : d146836 p = 1) : d152278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22515 q = 1) (hb : d146836 q = 1) : d152261 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22515, d152261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45944 q ha hb
    | true =>
      simp only [d22515, d152261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45945 q ha hb
  have h2 (q : Pattern) (ha : d22516 q = 1) (hb : d146836 q = 1) : d152262 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22516, d152262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22516, d152262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22517 q = 1) (hb : d146836 q = 1) : d152263 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22517, d152263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22517, d152263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22525 q = 1) (hb : d146836 q = 1) : d152265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22525, d152265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45945 q ha hb
    | true =>
      simp only [d22525, d152265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45946 q ha hb
  have h5 (q : Pattern) (ha : d22526 q = 1) (hb : d146836 q = 1) : d152266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22526, d152266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22526, d152266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22527 q = 1) (hb : d146836 q = 1) : d152267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22527, d152267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22527, d152267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22528 q = 1) (hb : d146836 q = 1) : d152268 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22528, d152268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22528, d152268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22535 q = 1) (hb : d146836 q = 1) : d152269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45945 q ha hb
    | true =>
      simp only [d22535, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
  have h9 (q : Pattern) (ha : d22536 q = 1) (hb : d146836 q = 1) : d152270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22537 q = 1) (hb : d146836 q = 1) : d152271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22544 q = 1) (hb : d146836 q = 1) : d152273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22544, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45947 q ha hb
  have h12 (q : Pattern) (ha : d22545 q = 1) (hb : d146836 q = 1) : d152274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22546 q = 1) (hb : d146836 q = 1) : d152275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22547 q = 1) (hb : d146836 q = 1) : d152276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22547, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22548 q = 1) (hb : d146836 q = 1) : d152277 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22548, d152277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22548, d152277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22549 q = 1) (hb : d146836 q = 1) : d152278 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22549, d152278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22549, d152278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro45949 (p : Pattern) (ha : d22554 p = 1) (hb : d146836 p = 1) : d152283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d146836 q = 1) : d152269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45945 q ha hb
    | true =>
      simp only [d22535, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d146836 q = 1) : d152270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d146836 q = 1) : d152271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22544 q = 1) (hb : d146836 q = 1) : d152273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22544, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45947 q ha hb
  have h5 (q : Pattern) (ha : d22545 q = 1) (hb : d146836 q = 1) : d152274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22546 q = 1) (hb : d146836 q = 1) : d152275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22547 q = 1) (hb : d146836 q = 1) : d152276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22552 q = 1) (hb : d146836 q = 1) : d152281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22552, d152281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22552, d152281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22553 q = 1) (hb : d146836 q = 1) : d152282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22553, d152282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22553, d152282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22554 q = 1) (hb : d146836 q = 1) : d152283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22554, d152283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22554, d152283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro45950 (p : Pattern) (ha : d22560 p = 1) (hb : d146836 p = 1) : d152289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22550 q = 1) (hb : d146836 q = 1) : d152279 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22550, d152279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45948 q ha hb
    | true =>
      simp only [d22550, d152279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22551 q = 1) (hb : d146836 q = 1) : d152280 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22551, d152280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22551, d152280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22555 q = 1) (hb : d146836 q = 1) : d152284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22555, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45949 q ha hb
    | true =>
      simp only [d22555, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22556 q = 1) (hb : d146836 q = 1) : d152285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22556, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22556, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22557 q = 1) (hb : d146836 q = 1) : d152286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22557, d152286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22557, d152286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22558 q = 1) (hb : d146836 q = 1) : d152287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22558, d152287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22558, d152287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22559 q = 1) (hb : d146836 q = 1) : d152288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22559, d152288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22559, d152288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22560 q = 1) (hb : d146836 q = 1) : d152289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22560, d152289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22560, d152289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45951 (p : Pattern) (ha : d22574 p = 1) (hb : d146836 p = 1) : d152301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22555 q = 1) (hb : d146836 q = 1) : d152284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22555, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45949 q ha hb
    | true =>
      simp only [d22555, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22556 q = 1) (hb : d146836 q = 1) : d152285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22556, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22556, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d146836 q = 1) : d152296 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45921 q ha hb
    | true =>
      simp only [d22569, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d146836 q = 1) : d152297 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22571 q = 1) (hb : d146836 q = 1) : d152298 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22571, d152298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22571, d152298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22572 q = 1) (hb : d146836 q = 1) : d152299 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22572, d152299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22572, d152299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22573 q = 1) (hb : d146836 q = 1) : d152300 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22573, d152300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22573, d152300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22574 q = 1) (hb : d146836 q = 1) : d152301 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22574, d152301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22574, d152301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45952 (p : Pattern) (ha : d22645 p = 1) (hb : d146836 p = 1) : d152305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d146836 q = 1) : d152269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45945 q ha hb
    | true =>
      simp only [d22535, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d146836 q = 1) : d152270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d146836 q = 1) : d152271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22544 q = 1) (hb : d146836 q = 1) : d152273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22544, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45947 q ha hb
  have h5 (q : Pattern) (ha : d22545 q = 1) (hb : d146836 q = 1) : d152274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22546 q = 1) (hb : d146836 q = 1) : d152275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22547 q = 1) (hb : d146836 q = 1) : d152276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22639 q = 1) (hb : d146836 q = 1) : d22639 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d22640 q = 1) (hb : d146836 q = 1) : d152290 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22640, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22640, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22641 q = 1) (hb : d146836 q = 1) : d152291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22641, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22641, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22642 q = 1) (hb : d146836 q = 1) : d152292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22642, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22642, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22643 q = 1) (hb : d146836 q = 1) : d152293 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22643, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22643, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22644 q = 1) (hb : d146836 q = 1) : d152304 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22644, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22644, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22645 q = 1) (hb : d146836 q = 1) : d152305 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22645, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22645, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro45953 (p : Pattern) (ha : d22651 p = 1) (hb : d146836 p = 1) : d152311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22646 q = 1) (hb : d146836 q = 1) : d152306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22646, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45952 q ha hb
    | true =>
      simp only [d22646, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22647 q = 1) (hb : d146836 q = 1) : d152307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22647, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22647, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22648 q = 1) (hb : d146836 q = 1) : d152308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22648, d152308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22648, d152308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22649 q = 1) (hb : d146836 q = 1) : d152309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22649, d152309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22649, d152309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22650 q = 1) (hb : d146836 q = 1) : d152310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22650, d152310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22650, d152310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22651 q = 1) (hb : d146836 q = 1) : d152311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22651, d152311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22651, d152311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45954 (p : Pattern) (ha : d146836 p = 1) (hb : d150223 p = 1) : d152317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22575 q = 1) (hb : d146836 q = 1) : d152302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22575, d152302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45950 q ha hb
    | true =>
      simp only [d22575, d152302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45951 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150219 q = 1) : d152303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150219, d152303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150219, d152303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22652 q = 1) (hb : d146836 q = 1) : d152312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22652, d152312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45953 q ha hb
    | true =>
      simp only [d22652, d152312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22653 q = 1) (hb : d146836 q = 1) : d152313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22653, d152313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22653, d152313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150220 q = 1) : d152314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150220, d152314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150220, d152314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150221 q = 1) : d152315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150221, d152315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150221, d152315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150222 q = 1) : d152316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150222, d152316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150222, d152316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150223 q = 1) : d152317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150223, d152317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150223, d152317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45955 (p : Pattern) (ha : d146836 p = 1) (hb : d150229 p = 1) : d152334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22282 q = 1) (hb : d146836 q = 1) : d152140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22282, d152140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22282, d152140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45910 q ha hb
  have h2 (q : Pattern) (ha : d22283 q = 1) (hb : d146836 q = 1) : d152141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22283, d152141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22283, d152141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22292 q = 1) (hb : d146836 q = 1) : d152150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45910 q ha hb
    | true =>
      simp only [d22292, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45913 q ha hb
  have h4 (q : Pattern) (ha : d22293 q = 1) (hb : d146836 q = 1) : d152151 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22293, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22294 q = 1) (hb : d146836 q = 1) : d152152 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d22294, d152152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22294, d152152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150207 q = 1) : d152229 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150207, d152229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45934 q ha hb
    | true =>
      simp only [d150207, d152229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45942 q ha hb
  have h7 (q : Pattern) (ha : d22483 q = 1) (hb : d146836 q = 1) : d152247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22483, d152247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45916 q ha hb
    | true =>
      simp only [d22483, d152247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45917 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150208 q = 1) : d152248 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150208, d152248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150208, d152248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150209 q = 1) : d152249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150209, d152249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150209, d152249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d150210 q = 1) : d152250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150210, d152250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150210, d152250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d150214 q = 1) : d152254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150214, d152254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150214, d152254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45943 q ha hb
  have h12 (q : Pattern) (ha : d22492 q = 1) (hb : d146836 q = 1) : d152256 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22492, d152256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22492, d152256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45918 q ha hb
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150215 q = 1) : d152257 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150215, d152257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150215, d152257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150216 q = 1) : d152258 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150216, d152258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150216, d152258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150217 q = 1) : d152259 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150217, d152259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150217, d152259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d150218 q = 1) : d152260 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150218, d152260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150218, d152260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146836 q = 1) (hb : d150224 q = 1) : d152318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150224, d152318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150224, d152318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45954 q ha hb
  have h18 (q : Pattern) (ha : d22669 q = 1) (hb : d146836 q = 1) : d152329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22669, d152329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22669, d152329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45923 q ha hb
  have h19 (q : Pattern) (ha : d146836 q = 1) (hb : d150225 q = 1) : d152330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150225, d152330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150225, d152330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d146836 q = 1) (hb : d150226 q = 1) : d152331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150226, d152331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150226, d152331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146836 q = 1) (hb : d150227 q = 1) : d152332 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150227, d152332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150227, d152332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146836 q = 1) (hb : d150228 q = 1) : d152333 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150228, d152333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150228, d152333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146836 q = 1) (hb : d150229 q = 1) : d152334 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150229, d152334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150229, d152334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro45956 (p : Pattern) (ha : d146836 p = 1) (hb : d150235 p = 1) : d152340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d150230 q = 1) : d152335 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150230, d152335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150230, d152335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45955 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150231 q = 1) : d152336 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150231, d152336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150231, d152336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d150232 q = 1) : d152337 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150232, d152337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150232, d152337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d150233 q = 1) : d152338 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150233, d152338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150233, d152338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150234 q = 1) : d152339 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150234, d152339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150234, d152339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150235 q = 1) : d152340 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150235, d152340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150235, d152340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45957 (p : Pattern) (ha : d22686 p = 1) (hb : d146836 p = 1) : d149531 p = 1 := by
  have h0 (q : Pattern) (ha : d22685 q = 1) (hb : d116750 q = 1) : d22685 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13682 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22686 q = 1) (hb : d146836 q = 1) : d149531 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22686, d146836, d149531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22686, d146836, d149531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45958 (p : Pattern) (ha : d22694 p = 1) (hb : d146836 p = 1) : d149535 p = 1 := by
  have h0 (q : Pattern) (ha : d22692 q = 1) (hb : d116750 q = 1) : d22692 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22693 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22694 q = 1) (hb : d146836 q = 1) : d149535 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22694, d146836, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22694, d146836, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45959 (p : Pattern) (ha : d22704 p = 1) (hb : d146836 p = 1) : d152348 p = 1 := by
  have h0 (q : Pattern) (ha : d22703 q = 1) (hb : d116750 q = 1) : d22703 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22704 q = 1) (hb : d146836 q = 1) : d152348 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22704, d146836, d152348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22704, d146836, d152348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45960 (p : Pattern) (ha : d22710 p = 1) (hb : d146836 p = 1) : d22854 p = 1 := by
  have h0 (q : Pattern) (ha : d22709 q = 1) (hb : d116750 q = 1) : d22709 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22710 q = 1) (hb : d146836 q = 1) : d22854 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22710, d146836, d22854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22710, d146836, d22854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45961 (p : Pattern) (ha : d22716 p = 1) (hb : d146836 p = 1) : d152358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d146836 q = 1) : d152345 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
    | true =>
      simp only [d22695, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d146836 q = 1) : d152346 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d146836 q = 1) : d152347 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22705 q = 1) (hb : d146836 q = 1) : d152349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22705, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45959 q ha hb
  have h5 (q : Pattern) (ha : d22706 q = 1) (hb : d146836 q = 1) : d152350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22707 q = 1) (hb : d146836 q = 1) : d152351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22708 q = 1) (hb : d146836 q = 1) : d152352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22711 q = 1) (hb : d146836 q = 1) : d152353 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22711, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22711, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45960 q ha hb
  have h9 (q : Pattern) (ha : d22712 q = 1) (hb : d146836 q = 1) : d152354 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22712, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22712, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22713 q = 1) (hb : d146836 q = 1) : d152355 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22713, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22713, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22714 q = 1) (hb : d146836 q = 1) : d152356 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22714, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22714, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22715 q = 1) (hb : d146836 q = 1) : d152357 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22715, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22715, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22716 q = 1) (hb : d146836 q = 1) : d152358 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22716, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22716, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro45962 (p : Pattern) (ha : d22720 p = 1) (hb : d146836 p = 1) : d152362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22711 q = 1) (hb : d146836 q = 1) : d152353 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22711, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22711, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45960 q ha hb
  have h2 (q : Pattern) (ha : d22712 q = 1) (hb : d146836 q = 1) : d152354 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22712, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22712, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22713 q = 1) (hb : d146836 q = 1) : d152355 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22713, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22713, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22714 q = 1) (hb : d146836 q = 1) : d152356 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22714, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22714, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22719 q = 1) (hb : d146836 q = 1) : d152361 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22719, d152361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22719, d152361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22720 q = 1) (hb : d146836 q = 1) : d152362 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22720, d152362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22720, d152362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45963 (p : Pattern) (ha : d22726 p = 1) (hb : d146836 p = 1) : d152368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45961 q ha hb
    | true =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d146836 q = 1) : d152366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22725 q = 1) (hb : d146836 q = 1) : d152367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22725, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22725, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22726 q = 1) (hb : d146836 q = 1) : d152368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22726, d152368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22726, d152368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45964 (p : Pattern) (ha : d22730 p = 1) (hb : d146836 p = 1) : d152372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d146836 q = 1) : d152370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22729 q = 1) (hb : d146836 q = 1) : d152371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22729, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22729, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22730 q = 1) (hb : d146836 q = 1) : d152372 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22730, d152372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22730, d152372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45965 (p : Pattern) (ha : d22736 p = 1) (hb : d146836 p = 1) : d152378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22731 q = 1) (hb : d146836 q = 1) : d152373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45963 q ha hb
    | true =>
      simp only [d22731, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45964 q ha hb
  have h2 (q : Pattern) (ha : d22732 q = 1) (hb : d146836 q = 1) : d152374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22732, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22733 q = 1) (hb : d146836 q = 1) : d152375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22733, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22734 q = 1) (hb : d146836 q = 1) : d152376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22734, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22735 q = 1) (hb : d146836 q = 1) : d152377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22736 q = 1) (hb : d146836 q = 1) : d152378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22736, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22736, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45966 (p : Pattern) (ha : d22739 p = 1) (hb : d146836 p = 1) : d152381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45961 q ha hb
    | true =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d146836 q = 1) : d152366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22725 q = 1) (hb : d146836 q = 1) : d152367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22725, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22725, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22739 q = 1) (hb : d146836 q = 1) : d152381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22739, d152381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22739, d152381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45967 (p : Pattern) (ha : d22740 p = 1) (hb : d146836 p = 1) : d152382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d146836 q = 1) : d152370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22729 q = 1) (hb : d146836 q = 1) : d152371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22729, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22729, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22740 q = 1) (hb : d146836 q = 1) : d152382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22740, d152382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22740, d152382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45968 (p : Pattern) (ha : d22746 p = 1) (hb : d146836 p = 1) : d152388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22731 q = 1) (hb : d146836 q = 1) : d152373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45963 q ha hb
    | true =>
      simp only [d22731, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45964 q ha hb
  have h2 (q : Pattern) (ha : d22732 q = 1) (hb : d146836 q = 1) : d152374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22732, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22733 q = 1) (hb : d146836 q = 1) : d152375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22733, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22734 q = 1) (hb : d146836 q = 1) : d152376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22734, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22735 q = 1) (hb : d146836 q = 1) : d152377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22741 q = 1) (hb : d146836 q = 1) : d152383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45966 q ha hb
    | true =>
      simp only [d22741, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45967 q ha hb
  have h7 (q : Pattern) (ha : d22742 q = 1) (hb : d146836 q = 1) : d152384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22743 q = 1) (hb : d146836 q = 1) : d152385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22743, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22744 q = 1) (hb : d146836 q = 1) : d152386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22745 q = 1) (hb : d146836 q = 1) : d152387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22746 q = 1) (hb : d146836 q = 1) : d152388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22746, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22746, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45969 (p : Pattern) (ha : d22783 p = 1) (hb : d146836 p = 1) : d152422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d146836 q = 1) : d152345 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
    | true =>
      simp only [d22695, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d146836 q = 1) : d152346 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d146836 q = 1) : d152347 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22705 q = 1) (hb : d146836 q = 1) : d152349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22705, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45959 q ha hb
  have h5 (q : Pattern) (ha : d22706 q = 1) (hb : d146836 q = 1) : d152350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22707 q = 1) (hb : d146836 q = 1) : d152351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22708 q = 1) (hb : d146836 q = 1) : d152352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22781 q = 1) (hb : d146836 q = 1) : d152420 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22781, d152420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22781, d152420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22782 q = 1) (hb : d146836 q = 1) : d152421 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22782, d152421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22782, d152421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22783 q = 1) (hb : d146836 q = 1) : d152422 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22783, d152422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22783, d152422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro45970 (p : Pattern) (ha : d22793 p = 1) (hb : d146836 p = 1) : d152432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22784 q = 1) (hb : d146836 q = 1) : d152423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45969 q ha hb
    | true =>
      simp only [d22784, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22785 q = 1) (hb : d146836 q = 1) : d152424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22790 q = 1) (hb : d146836 q = 1) : d152429 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22790, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22790, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22791 q = 1) (hb : d146836 q = 1) : d152430 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22791, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22791, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22792 q = 1) (hb : d146836 q = 1) : d152431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22792, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22792, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22793 q = 1) (hb : d146836 q = 1) : d152432 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22793, d152432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22793, d152432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45971 (p : Pattern) (ha : d22909 p = 1) (hb : d146836 p = 1) : d152478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22899 q = 1) (hb : d146836 q = 1) : d152468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22899, d152468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45970 q ha hb
    | true =>
      simp only [d22899, d152468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45964 q ha hb
  have h2 (q : Pattern) (ha : d22900 q = 1) (hb : d146836 q = 1) : d152469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22900, d152469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22900, d152469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22901 q = 1) (hb : d146836 q = 1) : d152470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22901, d152470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22901, d152470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22902 q = 1) (hb : d146836 q = 1) : d152471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22902, d152471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22902, d152471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22903 q = 1) (hb : d146836 q = 1) : d152472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22903, d152472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22903, d152472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22904 q = 1) (hb : d146836 q = 1) : d152473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22904, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45964 q ha hb
    | true =>
      simp only [d22904, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22905 q = 1) (hb : d146836 q = 1) : d152474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22905, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22905, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22906 q = 1) (hb : d146836 q = 1) : d152475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22906, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22906, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22907 q = 1) (hb : d146836 q = 1) : d152476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22907, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22907, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22908 q = 1) (hb : d146836 q = 1) : d152477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22908, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22908, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22909 q = 1) (hb : d146836 q = 1) : d152478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22909, d152478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22909, d152478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45972 (p : Pattern) (ha : d22915 p = 1) (hb : d146836 p = 1) : d152484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22904 q = 1) (hb : d146836 q = 1) : d152473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22904, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45964 q ha hb
    | true =>
      simp only [d22904, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22905 q = 1) (hb : d146836 q = 1) : d152474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22905, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22905, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22906 q = 1) (hb : d146836 q = 1) : d152475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22906, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22906, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22907 q = 1) (hb : d146836 q = 1) : d152476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22907, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22907, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22908 q = 1) (hb : d146836 q = 1) : d152477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22908, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22908, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22910 q = 1) (hb : d146836 q = 1) : d152479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22910, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45967 q ha hb
    | true =>
      simp only [d22910, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22911 q = 1) (hb : d146836 q = 1) : d152480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22911, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22911, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22912 q = 1) (hb : d146836 q = 1) : d152481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22912, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22912, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22913 q = 1) (hb : d146836 q = 1) : d152482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22913, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22913, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22914 q = 1) (hb : d146836 q = 1) : d152483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22914, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22914, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22915 q = 1) (hb : d146836 q = 1) : d152484 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22915, d152484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22915, d152484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45973 (p : Pattern) (ha : d22924 p = 1) (hb : d146836 p = 1) : d152493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22910 q = 1) (hb : d146836 q = 1) : d152479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22910, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45967 q ha hb
    | true =>
      simp only [d22910, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22911 q = 1) (hb : d146836 q = 1) : d152480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22911, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22911, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22912 q = 1) (hb : d146836 q = 1) : d152481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22912, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22912, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22913 q = 1) (hb : d146836 q = 1) : d152482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22913, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22913, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22914 q = 1) (hb : d146836 q = 1) : d152483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22914, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22914, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22924 q = 1) (hb : d146836 q = 1) : d152493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22924, d152493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22924, d152493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45974 (p : Pattern) (ha : d22948 p = 1) (hb : d146836 p = 1) : d149675 p = 1 := by
  have h0 (q : Pattern) (ha : d22947 q = 1) (hb : d116750 q = 1) : d22947 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22937 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22948 q = 1) (hb : d146836 q = 1) : d149675 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22948, d146836, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22948, d146836, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45975 (p : Pattern) (ha : d22976 p = 1) (hb : d146836 p = 1) : d23045 p = 1 := by
  have h0 (q : Pattern) (ha : d22975 q = 1) (hb : d116750 q = 1) : d22975 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15794 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22976 q = 1) (hb : d146836 q = 1) : d23045 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22976, d146836, d23045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22976, d146836, d23045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45976 (p : Pattern) (ha : d22982 p = 1) (hb : d146836 p = 1) : d152532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22977 q = 1) (hb : d146836 q = 1) : d152527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45974 q ha hb
    | true =>
      simp only [d22977, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45975 q ha hb
  have h2 (q : Pattern) (ha : d22978 q = 1) (hb : d146836 q = 1) : d152528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22979 q = 1) (hb : d146836 q = 1) : d152529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22980 q = 1) (hb : d146836 q = 1) : d152530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22980, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22981 q = 1) (hb : d146836 q = 1) : d152531 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22981, d152531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22981, d152531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22982 q = 1) (hb : d146836 q = 1) : d152532 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22982, d152532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22982, d152532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45977 (p : Pattern) (ha : d23068 p = 1) (hb : d146836 p = 1) : d152559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22983 q = 1) (hb : d146836 q = 1) : d152533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45976 q ha hb
    | true =>
      simp only [d22983, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22984 q = 1) (hb : d146836 q = 1) : d152534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23065 q = 1) (hb : d146836 q = 1) : d152556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23065, d152556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23065, d152556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23066 q = 1) (hb : d146836 q = 1) : d152557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23066, d152557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23066, d152557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23067 q = 1) (hb : d146836 q = 1) : d152558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23067, d152558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23067, d152558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23068 q = 1) (hb : d146836 q = 1) : d152559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23068, d152559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23068, d152559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45978 (p : Pattern) (ha : d23074 p = 1) (hb : d146836 p = 1) : d152565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23069 q = 1) (hb : d146836 q = 1) : d152560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23069, d152560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45977 q ha hb
    | true =>
      simp only [d23069, d152560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23070 q = 1) (hb : d146836 q = 1) : d152561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23070, d152561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23070, d152561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23071 q = 1) (hb : d146836 q = 1) : d152562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23071, d152562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23071, d152562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23072 q = 1) (hb : d146836 q = 1) : d152563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23072, d152563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23072, d152563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23073 q = 1) (hb : d146836 q = 1) : d152564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23073, d152564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23073, d152564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23074 q = 1) (hb : d146836 q = 1) : d152565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23074, d152565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23074, d152565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45979 (p : Pattern) (ha : d22751 p = 1) (hb : d146836 p = 1) : d152393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45961 q ha hb
    | true =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d146836 q = 1) : d152366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22750 q = 1) (hb : d146836 q = 1) : d152392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22750, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22750, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22751 q = 1) (hb : d146836 q = 1) : d152393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22751, d152393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22751, d152393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45980 (p : Pattern) (ha : d22753 p = 1) (hb : d146836 p = 1) : d152395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d146836 q = 1) : d152370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22752 q = 1) (hb : d146836 q = 1) : d152394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22752, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22752, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22753 q = 1) (hb : d146836 q = 1) : d152395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22753, d152395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22753, d152395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45981 (p : Pattern) (ha : d22760 p = 1) (hb : d146836 p = 1) : d152402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45961 q ha hb
    | true =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22758 q = 1) (hb : d146836 q = 1) : d152400 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22758, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22758, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22759 q = 1) (hb : d146836 q = 1) : d152401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22759, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22759, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22760 q = 1) (hb : d146836 q = 1) : d152402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22760, d152402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22760, d152402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45982 (p : Pattern) (ha : d22763 p = 1) (hb : d146836 p = 1) : d152405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22761 q = 1) (hb : d146836 q = 1) : d152403 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22761, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22761, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22762 q = 1) (hb : d146836 q = 1) : d152404 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22762, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22762, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22763 q = 1) (hb : d146836 q = 1) : d152405 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22763, d152405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22763, d152405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45983 (p : Pattern) (ha : d22768 p = 1) (hb : d146836 p = 1) : d149593 p = 1 := by
  have h0 (q : Pattern) (ha : d22767 q = 1) (hb : d116750 q = 1) : d22767 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17228 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22768 q = 1) (hb : d146836 q = 1) : d149593 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22768, d146836, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22768, d146836, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45984 (p : Pattern) (ha : d22772 p = 1) (hb : d146836 p = 1) : d13683 p = 1 := by
  have h0 (q : Pattern) (ha : d13682 q = 1) (hb : d116750 q = 1) : d13682 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22693 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22772 q = 1) (hb : d146836 q = 1) : d13683 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22772, d146836, d13683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22772, d146836, d13683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro45985 (p : Pattern) (ha : d22778 p = 1) (hb : d146836 p = 1) : d152417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22769 q = 1) (hb : d146836 q = 1) : d152409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22769, d152409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45983 q ha hb
    | true =>
      simp only [d22769, d152409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
  have h2 (q : Pattern) (ha : d22770 q = 1) (hb : d146836 q = 1) : d152410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22770, d152410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22770, d152410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22771 q = 1) (hb : d146836 q = 1) : d152411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22771, d152411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22771, d152411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22773 q = 1) (hb : d146836 q = 1) : d152412 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22773, d152412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
    | true =>
      simp only [d22773, d152412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45984 q ha hb
  have h5 (q : Pattern) (ha : d22774 q = 1) (hb : d146836 q = 1) : d152413 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22774, d152413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22774, d152413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22775 q = 1) (hb : d146836 q = 1) : d152414 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22775, d152414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22775, d152414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22776 q = 1) (hb : d146836 q = 1) : d152415 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22776, d152415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22776, d152415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22695 q = 1) (hb : d146836 q = 1) : d152345 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
    | true =>
      simp only [d22695, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
  have h9 (q : Pattern) (ha : d22696 q = 1) (hb : d146836 q = 1) : d152346 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22697 q = 1) (hb : d146836 q = 1) : d152347 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22705 q = 1) (hb : d146836 q = 1) : d152349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22705, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45959 q ha hb
  have h12 (q : Pattern) (ha : d22706 q = 1) (hb : d146836 q = 1) : d152350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22707 q = 1) (hb : d146836 q = 1) : d152351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22708 q = 1) (hb : d146836 q = 1) : d152352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22708, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22777 q = 1) (hb : d146836 q = 1) : d152416 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22777, d152416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22777, d152416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22778 q = 1) (hb : d146836 q = 1) : d152417 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22778, d152417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22778, d152417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro45986 (p : Pattern) (ha : d22789 p = 1) (hb : d146836 p = 1) : d152428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22779 q = 1) (hb : d146836 q = 1) : d152418 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22779, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45985 q ha hb
    | true =>
      simp only [d22779, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22780 q = 1) (hb : d146836 q = 1) : d152419 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22780, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22780, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22784 q = 1) (hb : d146836 q = 1) : d152423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45969 q ha hb
    | true =>
      simp only [d22784, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22785 q = 1) (hb : d146836 q = 1) : d152424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22786 q = 1) (hb : d146836 q = 1) : d152425 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22786, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22786, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22787 q = 1) (hb : d146836 q = 1) : d152426 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22787, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22787, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22788 q = 1) (hb : d146836 q = 1) : d152427 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22788, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22788, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22789 q = 1) (hb : d146836 q = 1) : d152428 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22789, d152428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22789, d152428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45987 (p : Pattern) (ha : d22860 p = 1) (hb : d146836 p = 1) : d152358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d146836 q = 1) : d152345 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
    | true =>
      simp only [d22695, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d146836 q = 1) : d152346 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d146836 q = 1) : d152347 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22705 q = 1) (hb : d146836 q = 1) : d152349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22705, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45959 q ha hb
  have h5 (q : Pattern) (ha : d22706 q = 1) (hb : d146836 q = 1) : d152350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22707 q = 1) (hb : d146836 q = 1) : d152351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22708 q = 1) (hb : d146836 q = 1) : d152352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22854 q = 1) (hb : d146836 q = 1) : d22854 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d22855 q = 1) (hb : d146836 q = 1) : d152353 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22855, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22855, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22856 q = 1) (hb : d146836 q = 1) : d152354 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22856, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22856, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22857 q = 1) (hb : d146836 q = 1) : d152355 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22857, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22857, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22858 q = 1) (hb : d146836 q = 1) : d152356 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22858, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22858, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22859 q = 1) (hb : d146836 q = 1) : d152357 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22859, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22859, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22860 q = 1) (hb : d146836 q = 1) : d152358 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22860, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22860, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro45988 (p : Pattern) (ha : d22866 p = 1) (hb : d146836 p = 1) : d152438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22861 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22861, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45987 q ha hb
    | true =>
      simp only [d22861, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22862 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22862, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22862, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22863 q = 1) (hb : d146836 q = 1) : d152435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22863, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22863, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22864 q = 1) (hb : d146836 q = 1) : d152436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22864, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22864, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22865 q = 1) (hb : d146836 q = 1) : d152437 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22865, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22865, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22866 q = 1) (hb : d146836 q = 1) : d152438 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22866, d152438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22866, d152438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45989 (p : Pattern) (ha : d146836 p = 1) (hb : d150244 p = 1) : d152444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22754 q = 1) (hb : d146836 q = 1) : d152396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22754, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45979 q ha hb
    | true =>
      simp only [d22754, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45980 q ha hb
  have h2 (q : Pattern) (ha : d22755 q = 1) (hb : d146836 q = 1) : d152397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22755, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22755, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22756 q = 1) (hb : d146836 q = 1) : d152398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22756, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22756, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22757 q = 1) (hb : d146836 q = 1) : d152399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22757, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22757, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22764 q = 1) (hb : d146836 q = 1) : d152406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22764, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45981 q ha hb
    | true =>
      simp only [d22764, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45982 q ha hb
  have h6 (q : Pattern) (ha : d22765 q = 1) (hb : d146836 q = 1) : d152407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22765, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22765, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22766 q = 1) (hb : d146836 q = 1) : d152408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22766, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22766, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22794 q = 1) (hb : d146836 q = 1) : d152433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22794, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45986 q ha hb
    | true =>
      simp only [d22794, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45970 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150240 q = 1) : d152434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150240, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22867 q = 1) (hb : d146836 q = 1) : d152439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22867, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45988 q ha hb
    | true =>
      simp only [d22867, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22868 q = 1) (hb : d146836 q = 1) : d152440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22868, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22868, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150241 q = 1) : d152441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150241, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150242 q = 1) : d152442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150242, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150243 q = 1) : d152443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150243, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d150244 q = 1) : d152444 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150244, d152444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150244, d152444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45990 (p : Pattern) (ha : d22873 p = 1) (hb : d146836 p = 1) : d152445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45961 q ha hb
    | true =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d146836 q = 1) : d152366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22750 q = 1) (hb : d146836 q = 1) : d152392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22750, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22750, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22873 q = 1) (hb : d146836 q = 1) : d152445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22873, d152445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22873, d152445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45991 (p : Pattern) (ha : d22874 p = 1) (hb : d146836 p = 1) : d152446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d146836 q = 1) : d152370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22752 q = 1) (hb : d146836 q = 1) : d152394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22752, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22752, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22874 q = 1) (hb : d146836 q = 1) : d152446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22874, d152446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22874, d152446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45992 (p : Pattern) (ha : d22879 p = 1) (hb : d146836 p = 1) : d152451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45961 q ha hb
    | true =>
      simp only [d22717, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146836 q = 1) : d152365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22758 q = 1) (hb : d146836 q = 1) : d152400 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22758, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22758, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22759 q = 1) (hb : d146836 q = 1) : d152401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22759, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22759, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22879 q = 1) (hb : d146836 q = 1) : d152451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22879, d152451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22879, d152451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45993 (p : Pattern) (ha : d22880 p = 1) (hb : d146836 p = 1) : d152452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146836 q = 1) : d152369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22761 q = 1) (hb : d146836 q = 1) : d152403 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22761, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22761, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22762 q = 1) (hb : d146836 q = 1) : d152404 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22762, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22762, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22880 q = 1) (hb : d146836 q = 1) : d152452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22880, d152452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22880, d152452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45994 (p : Pattern) (ha : d22884 p = 1) (hb : d146836 p = 1) : d152456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22779 q = 1) (hb : d146836 q = 1) : d152418 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22779, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45985 q ha hb
    | true =>
      simp only [d22779, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22780 q = 1) (hb : d146836 q = 1) : d152419 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22780, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22780, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22784 q = 1) (hb : d146836 q = 1) : d152423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45969 q ha hb
    | true =>
      simp only [d22784, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22785 q = 1) (hb : d146836 q = 1) : d152424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22786 q = 1) (hb : d146836 q = 1) : d152425 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22786, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22786, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22787 q = 1) (hb : d146836 q = 1) : d152426 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22787, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22787, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22788 q = 1) (hb : d146836 q = 1) : d152427 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22788, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22788, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22884 q = 1) (hb : d146836 q = 1) : d152456 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22884, d152456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22884, d152456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45995 (p : Pattern) (ha : d22885 p = 1) (hb : d146836 p = 1) : d152457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22784 q = 1) (hb : d146836 q = 1) : d152423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45969 q ha hb
    | true =>
      simp only [d22784, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22785 q = 1) (hb : d146836 q = 1) : d152424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146836 q = 1) : d152363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45962 q ha hb
    | true =>
      simp only [d22721, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146836 q = 1) : d152364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22790 q = 1) (hb : d146836 q = 1) : d152429 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22790, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22790, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22791 q = 1) (hb : d146836 q = 1) : d152430 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22791, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22791, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22792 q = 1) (hb : d146836 q = 1) : d152431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22792, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22792, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22885 q = 1) (hb : d146836 q = 1) : d152457 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22885, d152457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22885, d152457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45996 (p : Pattern) (ha : d22891 p = 1) (hb : d146836 p = 1) : d152460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22861 q = 1) (hb : d146836 q = 1) : d152359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22861, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45987 q ha hb
    | true =>
      simp only [d22861, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22862 q = 1) (hb : d146836 q = 1) : d152360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22862, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22862, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22863 q = 1) (hb : d146836 q = 1) : d152435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22863, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22863, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22864 q = 1) (hb : d146836 q = 1) : d152436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22864, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22864, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22865 q = 1) (hb : d146836 q = 1) : d152437 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22865, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22865, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22891 q = 1) (hb : d146836 q = 1) : d152460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22891, d152460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22891, d152460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45997 (p : Pattern) (ha : d146836 p = 1) (hb : d150249 p = 1) : d152466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22754 q = 1) (hb : d146836 q = 1) : d152396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22754, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45979 q ha hb
    | true =>
      simp only [d22754, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45980 q ha hb
  have h2 (q : Pattern) (ha : d22755 q = 1) (hb : d146836 q = 1) : d152397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22755, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22755, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22756 q = 1) (hb : d146836 q = 1) : d152398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22756, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22756, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22757 q = 1) (hb : d146836 q = 1) : d152399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22757, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22757, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22764 q = 1) (hb : d146836 q = 1) : d152406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22764, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45981 q ha hb
    | true =>
      simp only [d22764, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45982 q ha hb
  have h6 (q : Pattern) (ha : d22765 q = 1) (hb : d146836 q = 1) : d152407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22765, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22765, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22766 q = 1) (hb : d146836 q = 1) : d152408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22766, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22766, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22794 q = 1) (hb : d146836 q = 1) : d152433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22794, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45986 q ha hb
    | true =>
      simp only [d22794, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45970 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d150240 q = 1) : d152434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150240, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22867 q = 1) (hb : d146836 q = 1) : d152439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22867, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45988 q ha hb
    | true =>
      simp only [d22867, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22868 q = 1) (hb : d146836 q = 1) : d152440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22868, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22868, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d150241 q = 1) : d152441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150241, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d150242 q = 1) : d152442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150242, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d150243 q = 1) : d152443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150243, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22875 q = 1) (hb : d146836 q = 1) : d152447 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22875, d152447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45990 q ha hb
    | true =>
      simp only [d22875, d152447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45991 q ha hb
  have h16 (q : Pattern) (ha : d22876 q = 1) (hb : d146836 q = 1) : d152448 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22876, d152448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22876, d152448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22877 q = 1) (hb : d146836 q = 1) : d152449 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22877, d152449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22877, d152449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22878 q = 1) (hb : d146836 q = 1) : d152450 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22878, d152450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22878, d152450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22881 q = 1) (hb : d146836 q = 1) : d152453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22881, d152453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45992 q ha hb
    | true =>
      simp only [d22881, d152453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45993 q ha hb
  have h20 (q : Pattern) (ha : d22882 q = 1) (hb : d146836 q = 1) : d152454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22882, d152454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22882, d152454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d22883 q = 1) (hb : d146836 q = 1) : d152455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22883, d152455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22883, d152455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22886 q = 1) (hb : d146836 q = 1) : d152458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22886, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45994 q ha hb
    | true =>
      simp only [d22886, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45995 q ha hb
  have h23 (q : Pattern) (ha : d146836 q = 1) (hb : d150245 q = 1) : d152459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150245, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d22892 q = 1) (hb : d146836 q = 1) : d152461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22892, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45996 q ha hb
    | true =>
      simp only [d22892, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d22893 q = 1) (hb : d146836 q = 1) : d152462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22893, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22893, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d146836 q = 1) (hb : d150246 q = 1) : d152463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150246, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d146836 q = 1) (hb : d150247 q = 1) : d152464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150247, d152464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150247, d152464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d146836 q = 1) (hb : d150248 q = 1) : d152465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150248, d152465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150248, d152465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146836 q = 1) (hb : d150249 q = 1) : d152466 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150249, d152466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150249, d152466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro45998 (p : Pattern) (ha : d146836 p = 1) (hb : d150256 p = 1) : d152491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22886 q = 1) (hb : d146836 q = 1) : d152458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22886, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45994 q ha hb
    | true =>
      simp only [d22886, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45995 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d150245 q = 1) : d152459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150245, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22892 q = 1) (hb : d146836 q = 1) : d152461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22892, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45996 q ha hb
    | true =>
      simp only [d22892, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22893 q = 1) (hb : d146836 q = 1) : d152462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22893, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22893, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d150246 q = 1) : d152463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150246, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d150254 q = 1) : d152489 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150254, d152489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150254, d152489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d150255 q = 1) : d152490 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150255, d152490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150255, d152490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d150256 q = 1) : d152491 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150256, d152491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150256, d152491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45999 (p : Pattern) (ha : d22931 p = 1) (hb : d146836 p = 1) : d149666 p = 1 := by
  have h0 (q : Pattern) (ha : d22930 q = 1) (hb : d116750 q = 1) : d22930 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22931 q = 1) (hb : d146836 q = 1) : d149666 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22931, d146836, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22931, d146836, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
end NetHack.Soko22Hazard87
